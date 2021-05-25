{-# LANGUAGE CPP, ConstraintKinds, ImplicitParams, MultiWayIf, DeriveLift #-}
module Ohua.Standalone where

import Ohua.Prelude

import Control.Concurrent.Async.Lifted
import Control.Monad.RWS (tell, evalRWS)
import qualified Data.ByteString.Lazy.Char8 as L
import Data.Functor.Foldable hiding (fold)
import qualified Data.HashMap.Strict as HM
import Data.List (partition)
import qualified Data.HashSet as Set
import qualified Data.Text as T
import System.Directory
import System.FilePath as Path ((<.>), takeExtension)
import Control.Lens (each, view, (%~), (^?), ix, to, imap, imapped, at, non, _Just)
import Control.Monad.Trans.Control (MonadBaseControl)
import Language.Haskell.TH.Syntax (Lift)

import Ohua.ALang.Lang
import qualified Ohua.Frontend.Lang as Fr
import Ohua.Frontend.NS as NS
import Ohua.Unit
import Ohua.ALang.PPrint
import Ohua.Serialize.JSON ()

#ifdef WITH_SEXPR_PARSER
import qualified Ohua.Compat.SExpr.Lexer         as SLex
import qualified Ohua.Compat.SExpr.Parser        as SParse
#endif
#ifdef WITH_CLIKE_PARSER
import qualified Ohua.Compat.Clike.Parser        as CParse
import qualified Ohua.Compat.Clike.Types         as CTy
#endif
#ifdef WITH_ML_PARSER
import qualified Ohua.Compat.ML.Parser as MLParse
#endif

type LParserResult = RawNamespace
type LParser = L.ByteString -> LParserResult
data CombinedAnn e =
    CombinedAnn { typeAnn :: Maybe (FunAnn (TyExpr SomeBinding) ), genericAnn :: [e] }
    deriving (Show, Eq, Functor, Foldable, Traversable, Lift)

type TyAnnMap = HM.HashMap Binding (FunAnn (TyExpr SomeBinding))
type RawDecl = (Annotated (CombinedAnn Fr.Expr) Fr.Expr)
type Decl = (Annotated (CombinedAnn Expression) Expression )
type IFaceDefs = HashMap QualifiedBinding Decl
type ModMap = HashMap NSRef (MVar ResolvedNamespace)
type ModTracker = IORef ModMap
type RawNamespace = Namespace RawDecl
type ResolvedNamespace = Namespace Decl
type PreResolveHook = forall m. CompM m => RawNamespace -> m RawNamespace
type CompM m
     = (MonadIO m, MonadBaseControl IO m, MonadError Error m, MonadLogger m, ?env :: ResolutionEnv)
data ResolutionEnv = ResolutionEnv
    { preResolveHook :: PreResolveHook
    , modTracker :: ModTracker
    }

unannotatedNS :: Namespace e -> Namespace (Annotated (CombinedAnn e) e)
unannotatedNS = decls . each %~ Annotated (CombinedAnn Nothing [])

definedLangs :: [(Text, Text, LParser)]
definedLangs =
#ifdef WITH_SEXPR_PARSER
    ( ".ohuas"
    , "S-Expression frontend for the algorithm language"
    , unannotatedNS . SParse.parseNS . SLex.tokenize) :
#endif
#ifdef WITH_CLIKE_PARSER
    ( ".ohuac"
    , "C/Rust-like frontent for the algorithm language"
    , let reNS ::
                 (Namespace (Annotated (FunAnn CTy.RustTyExpr ) Fr.Expr), HashMap Binding [Fr.Expr])
              -> LParserResult
          reNS (ns, anns) = ns & decls %~ imap
              (\k v -> v & annotation .~ CombinedAnn
                        { typeAnn = Just $ v ^. annotation . to (fmap (view value))
                        , genericAnn = anns ^. at k . non [] })
       in reNS . CParse.parseNS) :
#endif
#ifdef WITH_ML_PARSER
    ( ".ohuaml"
    , "ML-style frontend for ALang"
    , unannotatedNS . MLParse.parseMod
    ) :
#endif
    []



getParser :: Text -> LParser
getParser ext
    | Just a <- find ((== ext) . view _1) definedLangs = a ^. _3
    | otherwise =
        error $ "No parser defined for files with extension '" <> ext <> "'"


stdNamespace :: (NSRef, [Binding])
stdNamespace =
    ( ["ohua", "lang"]
    , ["id", "smap", "if"] -- TODO complete list
     )

primitives :: HM.HashMap Binding Expression
primitives = HM.fromList []

resolveNS ::
       forall m. (MonadError Error m)
    => IFaceDefs
    -> ResolvedNamespace
    -> m ResolvedNamespace
resolveNS ifacem ns = do
    resDecls <-
        flip runReaderT (mempty, Set.fromMap $ ifacem $> ()) $
        go0
            (topSortDecls (`Set.member` locallyDefinedAlgos) $
             HM.toList (ns ^. decls))
    pure $ ns & decls .~ HM.fromList resDecls
  where
    go0 [] = pure []
    go0 ((varName, expr):xs) = do
        done <- go varName expr
        local (second $ Set.insert (QualifiedBinding (ns ^. name) varName)) $
            ((varName, done) :) <$> (go0 xs)
    go :: Binding -> Decl -> ReaderT (Set.HashSet Binding, Set.HashSet QualifiedBinding) m Decl
    go self = traverse $ cata (handleTerm self)
    handleTerm self e =
        case e of
            LetF bnd _ _ -> registered bnd
            VarF bnd
                | Just alangVersion <- primitives ^? ix bnd -> pure alangVersion
                | otherwise -> do
                    isLocal <- asks (Set.member bnd . fst)
                    let isSelf = bnd == self
                    if
                        | isLocal || isSelf -> pure $ Var bnd
                        | Just refer <- HM.lookup bnd refers ->
                            pure $ Lit (FunRefLit (FunRef refer Nothing))
                        | otherwise -> throwError $ "Binding not in scope " <> show bnd
            l@(LitF (FunRefLit (FunRef qb _))) -> do
                algoPresent <- asks (Set.member qb . snd)
                if | algoPresent || isImported qb -> recursed
                   | otherwise ->
                         throwError $
                         "No matching algo or stateful function available or namespace not loaded for " <>
                         show qb
            LambdaF bnd _ -> registered bnd
            _ -> recursed
      where
        recursed = embed <$> sequence e
        registered bnd = registerBnd bnd recursed
    isImported qb =
        (qb ^. namespace) `Set.member` Set.fromList (map fst sfImports1)
    sfImports1 = stdNamespace : ns ^. sfImports
    registerBnd = local . first . Set.insert
    locallyDefinedAlgos = Set.fromList $ HM.keys (ns ^. decls)
    refers = HM.union
        (mkReferMap $ (ns ^. name, HM.keys (ns ^. decls)) : ns ^. algoImports)
        (mkReferMap sfImports1)
    mkReferMap importList =
        HM.fromListWith
            reportCollidingRef
            [ (shortname, QualifiedBinding sourceNS shortname)
            | (sourceNS, referList) <- importList
            , shortname <- referList
            ]
    reportCollidingRef a b =
        error $
        "Colliding refer for '" <> show a <> "' and '" <> show b <> "' in " <>
        show (ns ^. name)

inlineAlgos :: MonadIO m => ModMap -> Expr -> m Expr
inlineAlgos m = rewriteM $ \case
    Lit (FunRefLit (FunRef r _)) | Just modVar <- m ^? ix (r^.namespace) -> do
                                       mod <- maybe (error $ "Namespaces must be loaded at this point " <> show (r^.namespace)) pure =<< tryTakeMVar modVar
                                       pure $ mod ^? decls . ix (r^.name) . value
    _ -> pure Nothing

readAndParse ::
       (MonadLogger m, MonadIO m) => Text -> m LParserResult
readAndParse filename = do
    r <- getParser ext <$>
        liftIO (L.readFile strFname)
    logDebugN $ "Raw parse result for " <> filename
    logDebugN $ "<Pretty printing not implemented for frontend lang yet>" -- quickRender ns
    logDebugN "With type annotations:"
    logDebugN $ show (decls . each . annotation %~ typeAnn $ r)
    logDebugN $ "And annotations:"
    logDebugN $ show (decls . each . annotation %~ genericAnn $ r)
    pure r
  where
    strFname = toString filename
    ext = toText $ takeExtension strFname


gatherDeps :: CompM m => [NSRef] -> m IFaceDefs
gatherDeps namespaces = do
    mods <- mapConcurrently registerAndLoad namespaces
    pure $ HM.fromList
        [ (QualifiedBinding (depNamespace ^. NS.name) depName, algo)
        | depNamespace <- mods
        , (depName, algo) <- HM.toList $ depNamespace ^. decls
        ]


findSourceFile :: (MonadError Error m, MonadIO m) => NSRef -> m Text
findSourceFile modname = do
    candidates <-
        filterM (liftIO . doesFileExist) $
        map ((asFile Path.<.>) . toString) extensions
    case candidates of
        [] -> throwError $ "No file found for module " <> show modname
        [f] -> pure $ toText f
        files ->
            throwError $
            "Found multiple files matching " <> show modname <> ": " <>
            show files
  where
    asFile = toString $ T.intercalate "/" $ map unwrap $ unwrap modname
    extensions = map (^. _1) definedLangs


loadModule :: CompM m => NSRef -> m ResolvedNamespace
loadModule modname = do
    filename <- findSourceFile modname
    rawMod <- readAndParse filename
    unless (rawMod ^. name == modname) $
        throwError $
        "Expected module with name " <> show modname <> " but got " <>
        show (rawMod ^. name)
    loadDepsAndResolve rawMod


loadDepsAndResolve ::
       CompM m => RawNamespace -> m ResolvedNamespace
loadDepsAndResolve =
    preResolveHook ?env >=> \rawMod ->
        join $
        resolveNS <$> gatherDeps (map fst $ rawMod ^. algoImports) <*>
        runGenBndT mempty ((decls . traverse) (\(Annotated ann val) -> Annotated <$> (traverse Fr.toAlang ann) <*> Fr.toAlang val) rawMod)

registerAndLoad :: CompM m => NSRef -> m ResolvedNamespace
registerAndLoad reference =
    registerAnd reference (loadModule reference)


insertDirectly ::
       MonadIO m
    => ModTracker
    -> ResolvedNamespace
    -> m (MVar ResolvedNamespace)
insertDirectly tracker ns = do
    nsRef <- newMVar ns
    modifyIORef' tracker $ HM.insert (ns ^. name) nsRef
    pure nsRef

registerAnd ::
       (MonadIO m, ?env :: ResolutionEnv)
    => NSRef
    -> m ResolvedNamespace
    -> m ResolvedNamespace
registerAnd reference ac = do
    newModRef <- liftIO newEmptyMVar
    actualRef <-
        liftIO $
        atomicModifyIORef' (modTracker ?env) $ \trackerMap ->
            case trackerMap ^? ix reference of
                Just mvar -> (trackerMap, Left mvar)
                Nothing ->
                    (HM.insert reference newModRef trackerMap, Right newModRef)
    case actualRef of
        Left toWait -> liftIO $ readMVar toWait
        Right build -> do
            compiled <- ac
            liftIO $ putMVar build compiled
            pure compiled


gatherSFDeps :: Expression -> Set.HashSet QualifiedBinding
gatherSFDeps e = Set.fromList [ref | Lit (FunRefLit (FunRef ref _)) <- universe e]
-- gatherSFDeps = cata $ \case
--   VarF (Sf ref _) -> Set.singleton ref
--   other -> fold other


topSortMods :: [Namespace a] -> [Namespace a]
topSortMods = topSortWith (^. name) (map fst . view algoImports)


topSortWith :: (Hashable b, Eq b) => (a -> b) -> (a -> [b]) -> [a] -> [a]
topSortWith getIdent getDeps mods' =
    concat @[] $ ana (uncurry go) (mempty, mods')
  where
    go satisfied avail
        | null newSat =
            if null newAvail
                then Nil
                else error "Unsortable! (Probably due to a cycle)"
        | otherwise =
            Cons newSat $
            (Set.union (Set.fromList (map getIdent newSat)) satisfied, newAvail)
      where
        (newSat, newAvail) =
            partition (all (`Set.member` satisfied) . getDeps) avail


topSortDecls :: HasValue e e Expr Expr => (Binding -> Bool) -> [(Binding, e)] -> [(Binding, e)]
topSortDecls f declarations = map fst $ topSortWith (fst . fst) snd declsWDeps
  where
    localAlgos = Set.fromList $ map fst declarations
    getDeps (item, e) =
        Set.toList $
        Set.delete item $
        snd $ evalRWS (go $ e ^. value) mempty ()
      where
        go =
            cata $ \e ->
                let recursed = sequence_ e
                    registered bnd = local (Set.insert bnd) recursed
                 in case e of
                        LetF bnd val body -> registered bnd
                        VarF bnd
                            | f bnd ->
                                unlessM (asks $ Set.member bnd) $
                                when (bnd `Set.member` localAlgos) $ tell [bnd]
                        LambdaF bnd body -> registered bnd
                        _ -> recursed
    declsWDeps = zip declarations $ map getDeps declarations


mainToEnv :: Expression -> (Int, Expression)
mainToEnv = go 0 identity
  where
    go !i f (Lambda assignment body) =
        go (i + 1) (f . Let assignment (Lit $ EnvRefLit $ makeThrow i)) body
    go !i f rest = (i, f rest)

typeFormatterHelper :: Text -> TyExpr SomeBinding -> TyExpr SomeBinding -> Text
typeFormatterHelper moduleSeparator tupleConstructor = go []
  where
    formatRef sb = T.intercalate moduleSeparator $ map unwrap bnds
      where
        bnds =
            case sb of
                Unqual b -> [b]
                Qual (QualifiedBinding ns bnd) -> unwrap ns ++ [bnd]
    go l e
        | e == tupleConstructor = "(" <> arglist <> ")"
        | otherwise =
            case e of
                TyRef ref ->
                    formatRef ref <>
                    if null l
                        then ""
                        else "<" <> arglist <> ">"
                TyApp t1 t2 -> go (go [] t2 : l) t1
      where
        arglist = T.intercalate "," l

#if WITH_CLIKE_PARSER
formatRustType :: TyExpr SomeBinding -> Text
formatRustType = typeFormatterHelper "::" CTy.tupleConstructor
#endif
type LangFormatter = TyExpr SomeBinding -> Text

langs :: [(Text, LangFormatter)]
langs =
#if WITH_CLIKE_PARSER
  ("rust", formatRustType) :
#endif
  []
