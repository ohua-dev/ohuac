{-# LANGUAGE CPP, ConstraintKinds #-}
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
import Control.Lens (each, view, (%~), (^?), ix)
import Control.Monad.Trans.Control (MonadBaseControl)

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

type LParser = L.ByteString -> (Maybe TyAnnMap, RawNamespace)

definedLangs :: [(Text, Text, LParser)]
definedLangs =
#ifdef WITH_SEXPR_PARSER
    ( ".ohuas"
    , "S-Expression frontend for the algorithm language"
    , (Nothing, ) . SParse.parseNS . SLex.tokenize) :
#endif
#ifdef WITH_CLIKE_PARSER
    ( ".ohuac"
    , "C/Rust-like frontent for the algorithm language"
    , let reNS ::
                 Namespace (Annotated (FunAnn (TyExpr SomeBinding)) Fr.Expr)
              -> (Maybe TyAnnMap, RawNamespace)
          reNS ns =
              (Just $ HM.fromList anns, ns & decls .~ HM.fromList newDecls)
            where
              (anns, newDecls) =
                  unzip $
                  map
                      (\(bnd, Annotated tyAnn expr) ->
                           ((bnd, tyAnn), (bnd, expr)))
                      (HM.toList $ ns ^. decls)
          remMutAnn = decls . each . annotation %~ fmap (view value)
       in reNS . remMutAnn . CParse.parseNS) :
#endif
#ifdef WITH_ML_PARSER
    ( ".ohuaml"
    , "ML-style frontend for ALang"
    , (Nothing, ) . MLParse.parseMod
    ) :
#endif
    []



getParser :: Text -> L.ByteString -> (Maybe TyAnnMap, RawNamespace)
getParser ext
    | Just a <- find ((== ext) . view _1) definedLangs = a ^. _3
    | otherwise =
        error $ "No parser defined for files with extension '" <> ext <> "'"


type IFaceDefs = HashMap QualifiedBinding Expression
type ModMap = HashMap NSRef (MVar ResolvedNamespace)
type ModTracker = IORef ModMap
type RawNamespace = Namespace (Fr.Expr)
type ResolvedNamespace = Namespace Expression
type CompM m
     = (MonadIO m, MonadBaseControl IO m, MonadError Error m, MonadLogger m)
type TyAnnMap = HM.HashMap Binding (FunAnn (TyExpr SomeBinding))


stdNamespace :: (NSRef, [Binding])
stdNamespace =
    ( ["ohua", "lang"]
    , ["id", "smap", "if"] -- TODO complete list
     )

primitives :: HM.HashMap Binding Expression
primitives = HM.fromList []

resolveNS ::
       forall m. MonadError Error m
    => IFaceDefs
    -> ResolvedNamespace
    -> m ResolvedNamespace
resolveNS ifacem ns = do
    resDecls <-
        flip runReaderT (mempty, ifacem) $
        go0
            (topSortDecls (`Set.member` locallyDefinedAlgos) $
             HM.toList (ns ^. decls))
    pure $ ns & decls .~ HM.fromList resDecls
  where
    go0 [] = pure []
    go0 ((varName, expr):xs) = do
        done <- go expr
        local (second $ HM.insert (QualifiedBinding (ns ^. name) varName) done) $
            ((varName, done) :) <$> (go0 xs)
    go :: Expr -> ReaderT (Set.HashSet Binding, IFaceDefs) m Expression
    go = cata handleTerm
    handleTerm e =
        case e of
            LetF bnd val body -> registered bnd
            VarF bnd
                | Just alangVersion <- primitives ^? ix bnd -> pure alangVersion
                | otherwise -> do
                    isLocal <- asks (Set.member bnd . fst)
                    if isLocal
                        then pure $ Var bnd
                        else case ( HM.lookup bnd algoRefers
                                  , HM.lookup bnd sfRefers) of
                                 (Just algo, Just sf) ->
                                     throwError $
                                     "Ambiguous ocurrence of unqualified binding " <>
                                     show bnd <>
                                     ". Could refer to algo " <>
                                     show algo <>
                                     " or sf " <>
                                     show sf
                                 (Just algoname, _) ->
                                     maybe
                                         (throwError $
                                          "Algo not loaded " <> show algoname)
                                         pure =<<
                                     asks (HM.lookup algoname . snd)
                                 (_, Just sf) -> pure $ Lit $ FunRefLit $ FunRef sf Nothing
                                 _ ->
                                     throwError $
                                     "Binding not in scope " <> show bnd
            LitF (FunRefLit (FunRef qb _)) -> do
                algo <- asks (HM.lookup qb . snd)
                case algo of
                    Just anAlgo -> pure anAlgo
                    _
                        | isImported qb -> pure $ Lit $ FunRefLit $ FunRef qb Nothing
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
    algoRefers =
        mkReferMap $ (ns ^. name, HM.keys (ns ^. decls)) : ns ^. algoImports
    sfRefers = mkReferMap sfImports1
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

readAndParse ::
       (MonadLogger m, MonadIO m) => Text -> m (Maybe TyAnnMap, RawNamespace)
readAndParse filename = do
    (anns, ns) <-
        let strFname = toString filename
         in getParser (toText $ takeExtension strFname) <$>
            liftIO (L.readFile strFname)
    logDebugN $ "Raw parse result for " <> filename
    logDebugN $ "<Pretty printing not implemented for frontend lang yet>" -- quickRender ns
    logDebugN "With annotations:"
    logDebugN $ show anns
    pure (anns, ns)


gatherDeps :: CompM m => IORef ModMap -> [NSRef] -> m IFaceDefs
gatherDeps tracker namespaces = do
    mods <- mapConcurrently (registerAndLoad tracker) namespaces
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


loadModule :: CompM m => ModTracker -> NSRef -> m ResolvedNamespace
loadModule tracker modname = do
    filename <- findSourceFile modname
    (_anns, rawMod) <- readAndParse filename
    unless (rawMod ^. name == modname) $
        throwError $
        "Expected module with name " <> show modname <> " but got " <>
        show (rawMod ^. name)
    loadDepsAndResolve tracker rawMod


loadDepsAndResolve ::
       CompM m => ModTracker -> RawNamespace -> m ResolvedNamespace
loadDepsAndResolve tracker rawMod =
    join $
    resolveNS <$> gatherDeps tracker (map fst $ rawMod ^. algoImports) <*>
    runGenBndT mempty ((decls . traverse) Fr.toAlang rawMod)

registerAndLoad :: CompM m => ModTracker -> NSRef -> m ResolvedNamespace
registerAndLoad tracker reference =
    registerAnd tracker reference (loadModule tracker reference)


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
       (Eq ref, Hashable ref, MonadIO m)
    => IORef (HashMap ref (MVar load))
    -> ref
    -> m load
    -> m load
registerAnd tracker reference ac = do
    newModRef <- liftIO newEmptyMVar
    actualRef <-
        liftIO $
        atomicModifyIORef' tracker $ \trackerMap ->
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


topSortDecls :: (Binding -> Bool) -> [(Binding, Expr)] -> [(Binding, Expr)]
topSortDecls f declarations = map fst $ topSortWith (fst . fst) snd declsWDeps
  where
    localAlgos = Set.fromList $ map fst declarations
    getDeps e = Set.toList $ snd $ evalRWS (go e) mempty ()
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
    declsWDeps = zip declarations $ map (getDeps . snd) declarations


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
