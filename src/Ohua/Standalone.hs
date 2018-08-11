{-# LANGUAGE CPP #-}
module Ohua.Standalone where

import Protolude

import Control.Concurrent.Async.Lifted
import Control.Monad.RWS
import Control.Monad.Writer
import Data.Aeson as A
import qualified Data.ByteString.Lazy.Char8 as L
import Data.Default.Class
import Data.Functor.Foldable hiding (fold)
import Data.Generics.Uniplate.Direct
import qualified Data.HashMap.Strict as HM
import Data.IORef
import Data.List (partition)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as T
import GHC.Generics
import Lens.Micro
import Lens.Micro.Internal (Index, IxValue, Ixed)
import Lens.Micro.Mtl
import System.Directory
import System.FilePath as Path ((<.>), takeExtension)

import Ohua.ALang.Lang
import Ohua.ALang.NS as NS
import Ohua.Compile
import Ohua.DFGraph
import Ohua.DFGraph.File
import qualified Ohua.LensClasses as OLC
import Ohua.Monad
import Ohua.Serialize.JSON ()
import Ohua.Types
import Ohua.Util.Str (showS)
import qualified Ohua.Util.Str as Str

#ifdef WITH_SEXPR_PARSER
import qualified Ohua.Compat.SExpr.Lexer         as SLex
import qualified Ohua.Compat.SExpr.Parser        as SParse
#endif
#ifdef WITH_CLIKE_PARSER
import qualified Ohua.Compat.Clike.Parser        as CParse
import qualified Ohua.Compat.Clike.Types         as CTy
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
                 Namespace (Annotated (FunAnn (TyExpr SomeBinding)) (Expr SomeBinding))
              -> (Maybe TyAnnMap, RawNamespace)
          reNS ns =
              (Just $ HM.fromList anns, ns & decls .~ HM.fromList newDecls)
            where
              (anns, newDecls) =
                  unzip $
                  map
                      (\(name, Annotated tyAnn expr) ->
                           ((name, tyAnn), (name, expr)))
                      (HM.toList $ ns ^. decls)
          remMutAnn = decls . each . OLC.annotation %~ fmap (view OLC.value)
       in reNS . remMutAnn . CParse.parseNS) :
#endif
    []



getParser :: Text -> L.ByteString -> (Maybe TyAnnMap, RawNamespace)
getParser ext
    | Just a <- find ((== ext) . view _1) definedLangs = a ^. _3
    | otherwise =
        panic $ "No parser defined for files with extension '" <> ext <> "'"


type IFaceDefs = Map QualifiedBinding Expression
type ModMap = Map NSRef (MVar ResolvedNamespace)
type ModTracker = IORef ModMap
type RawNamespace = Namespace (Expr SomeBinding)
type ResolvedNamespace = Namespace Expression
type CompM = ExceptT Error (LoggingT IO)
type TyAnnMap = HM.HashMap Binding (FunAnn (TyExpr SomeBinding))


stdNamespace :: (NSRef, [Binding])
stdNamespace =
    ( ["ohua", "lang"]
    , ["id", "smap", "if"] -- TODO complete list
     )


resolveNS ::
       forall m. MonadError Error m
    => IFaceDefs
    -> RawNamespace
    -> m ResolvedNamespace
resolveNS ifacem ns@(Namespace modname algoImports sfImports' decls) = do
    resDecls <-
        flip runReaderT (mempty, ifacem) $
        go0
            (topSortDecls
                 (\case
                      Unqual bnd
                          | bnd `Set.member` locallyDefinedAlgos -> Just bnd
                      _ -> Nothing) $
             HM.toList decls)
    pure $ ns & NS.decls .~ HM.fromList resDecls
  where
    go0 [] = pure []
    go0 ((name, expr):xs) = do
        done <- go expr
        local (second $ Map.insert (QualifiedBinding modname name) done) $
            ((name, done) :) <$> (go0 xs)
    go :: Expr SomeBinding
       -> ReaderT (Set.Set Binding, IFaceDefs) m Expression
    go (Let assign val body) =
        registerAssign assign $ Let assign <$> go val <*> go body
    go (Var (Unqual bnd)) = do
        isLocal <- asks (Set.member bnd . fst)
        if isLocal
            then pure $ Var $ Local bnd
            else case (Map.lookup bnd algoRefers, Map.lookup bnd sfRefers) of
                     (Just algo, Just sf) ->
                         throwError $
                         "Ambiguous ocurrence of unqualified binding " <>
                         showS bnd <>
                         ". Could refer to algo " <>
                         showS algo <>
                         " or sf " <>
                         showS sf
                     (Just algoname, _) ->
                         maybe
                             (throwError $ "Algo not loaded " <> showS algoname)
                             pure =<<
                         asks (Map.lookup algoname . snd)
                     (_, Just sf) -> pure $ Var $ Sf sf Nothing
                     _ -> throwError $ "Binding not in scope " <> showS bnd
    go (Var (Qual qb)) = do
        algo <- asks (Map.lookup qb . snd)
        case algo of
            Just algo -> pure algo
            _
                | qbNamespace qb `Set.member` importedSfNamespaces ->
                    pure $ Var (Sf qb Nothing)
            _ ->
                throwError $
                "No matching algo available or namespace not loaded for " <>
                showS qb
    go (Apply expr expr2) = Apply <$> go expr <*> go expr2
    go (Lambda assign body) = registerAssign assign $ Lambda assign <$> go body
    sfImports = stdNamespace : sfImports'
    registerAssign = local . first . Set.union . Set.fromList . extractBindings
    locallyDefinedAlgos = Set.fromList $ HM.keys decls
    importedSfNamespaces = Set.fromList $ map fst sfImports
    algoRefers = mkReferMap $ (modname, HM.keys decls) : algoImports
    sfRefers = mkReferMap sfImports
    mkReferMap importList =
        Map.fromListWith
            reportCollidingRef
            [ (shortname, QualifiedBinding sourceNS shortname)
            | (sourceNS, referList) <- importList
            , shortname <- referList
            ]
    reportCollidingRef a b =
        panic $
        "Colliding refer for '" <> show a <> "' and '" <> show b <> "' in " <>
        show modname

withS :: (StringConv a b, StringConv b c) => (b -> b) -> a -> c
withS f = toS . f . toS

readAndParse :: MonadIO m => Text -> m (Maybe TyAnnMap, RawNamespace)
readAndParse filename = getParser (withS takeExtension filename) <$> liftIO (L.readFile $ toS filename)


gatherDeps :: IORef ModMap -> Namespace a -> CompM IFaceDefs
gatherDeps tracker ns = do
    mods <- mapConcurrently (registerAndLoad tracker) (map fst $ ns ^. algoImports)
    pure $ Map.fromList
        [ (QualifiedBinding (depNamespace ^. NS.name) depName, algo)
        | depNamespace <- mods
        , (depName, algo) <- HM.toList $ depNamespace ^. decls
        ]


findSourceFile :: NSRef -> CompM Text
findSourceFile modname = do
    candidates <- filterM (liftIO . doesFileExist) $ map ((asFile Path.<.>) . toS) extensions
    case candidates of
        [] -> throwError $ "No file found for module " <> showS modname
        [f] -> pure $ toS f
        files -> throwError $ "Found multiple files matching " <> showS modname <> ": " <> showS files
  where
    asFile = intercalate "/" $ map (Str.toString . unwrap) $ unwrap modname
    extensions = map (^. _1) definedLangs


loadModule :: ModTracker -> NSRef -> CompM ResolvedNamespace
loadModule tracker modname = do
    filename <- findSourceFile modname
    (_anns, rawMod) <- readAndParse filename
    unless (rawMod ^. name == modname) $
        throwError $ "Expected module with name " <> Str.showS modname <> " but got " <> Str.showS (rawMod ^. name)
    loadDepsAndResolve tracker rawMod


loadDepsAndResolve :: ModTracker -> RawNamespace -> CompM ResolvedNamespace
loadDepsAndResolve tracker rawMod = flip resolveNS rawMod =<< gatherDeps tracker rawMod


registerAndLoad :: ModTracker -> NSRef -> CompM ResolvedNamespace
registerAndLoad tracker reference = registerAnd tracker reference (loadModule tracker reference)


registerAnd :: (Eq ref, Ord ref) => IORef (Map ref (MVar load)) -> ref -> CompM load -> CompM load
registerAnd tracker reference ac = do
    newModRef <- liftIO newEmptyMVar
    actualRef <- liftIO $ atomicModifyIORef' tracker $ \trackerMap ->
        case trackerMap ^? ix reference of
            Just mvar -> (trackerMap, Left mvar)
            Nothing   -> (Map.insert reference newModRef trackerMap, Right newModRef)
    case actualRef of
        Left toWait -> liftIO $ readMVar toWait
        Right build -> do
            compiled <- ac
            liftIO $ putMVar build compiled
            pure compiled


gatherSFDeps :: Expression -> Set.Set QualifiedBinding
gatherSFDeps e = Set.fromList [ref | Var (Sf ref _) <- universe e]
-- gatherSFDeps = cata $ \case
--   VarF (Sf ref _) -> Set.singleton ref
--   other -> fold other


topSortMods :: [Namespace ResolvedSymbol] -> [Namespace ResolvedSymbol]
topSortMods = topSortWith (^. name) (map fst . view algoImports)


topSortWith :: (Ord b, Eq b) => (a -> b) -> (a -> [b]) -> [a] -> [a]
topSortWith getIdent getDeps mods' = concat @[] $ ana (uncurry go) (mempty, mods')
  where
    go satisfied avail
      | null newSat =
        if null newAvail
        then Nil
        else panic "Unsortable! (Probably due to a cycle)"
      | otherwise = Cons newSat $ (Set.union (Set.fromList (map getIdent newSat)) satisfied, newAvail)
      where
        (newSat, newAvail) = partition (all (`Set.member` satisfied) . getDeps) avail


topSortDecls :: (a -> Maybe Binding) -> [(Binding, Expr a)] -> [(Binding, Expr a)]
topSortDecls f declarations = map fst $ topSortWith (fst . fst) snd declsWDeps
  where
    localAlgos = Set.fromList $ map fst declarations
    getDeps e = Set.toList $ snd $ evalRWS (go e) mempty ()
      where
        go =
            cata $ \case
                LetF assignment val body -> withRegisterBinds assignment $ val >> body
                VarF thing
                    | Just bnd <- f thing ->
                        unlessM (asks $ Set.member bnd) $
                        when (bnd `Set.member` localAlgos) $ tell [bnd]
                LambdaF assignment body -> withRegisterBinds assignment body
                expression -> sequence_ expression
        withRegisterBinds = local . Set.union . Set.fromList . extractBindings
    declsWDeps = zip declarations $ map (getDeps . snd) declarations


mainToEnv :: Expression -> (Int, Expression)
mainToEnv = go 0 identity
  where
    go !i f (Lambda assignment body) =
        go (i + 1) (f . Let assignment (Var $ Env $ makeThrow i)) body
    go !i f rest = (i, f rest)

typeFormatterHelper :: Text -> TyExpr SomeBinding -> TyExpr SomeBinding -> Text
typeFormatterHelper moduleSeparator tupleConstructor = go []
  where
    formatRef sb =
        T.intercalate moduleSeparator (map (toS . Str.toString . unwrap) bnds)
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
