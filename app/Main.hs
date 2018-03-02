{-# LANGUAGE CPP              #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE TypeApplications #-}
module Main where


import           Control.Arrow
import           Control.Concurrent.Async.Lifted
import           Control.Concurrent.MVar.Lifted
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.IO.Class
import           Control.Monad.Reader
import           Control.Monad.RWS
import           Control.Monad.Writer
import           Data.Aeson                      as A
import qualified Data.ByteString.Lazy.Char8      as L
import qualified Data.Char                       as C
import           Data.Default.Class
import           Data.Foldable
import           Data.Functor.Foldable           hiding (fold)
import           Data.Hashable
import qualified Data.HashMap.Strict             as HM
import qualified Data.HashSet                    as HS
import           Data.IORef.Lifted
import           Data.List                       (partition)
import           Data.List                       (intercalate, intersperse)
import           Data.Maybe
import           Data.Monoid
import           Data.String                     (fromString)
import qualified Data.Text                       as T
import           GHC.Generics
import           Lens.Micro
import           Lens.Micro.Mtl
import           Ohua.ALang.Lang
import           Ohua.ALang.NS                   as NS
import           Ohua.Compile
import           Ohua.DFGraph
import qualified Ohua.LensClasses                as OLC
import           Ohua.Monad
import           Ohua.Serialize.JSON
import           Ohua.Types
import           Ohua.Util.Str                   (showS)
import qualified Ohua.Util.Str                   as Str
import           Options.Applicative
import           System.Directory
import           System.Environment
import           System.FilePath                 (takeExtension, (-<.>), (<.>))

#ifdef WITH_SEXPR_PARSER
import qualified Ohua.Compat.SExpr.Lexer         as SLex
import qualified Ohua.Compat.SExpr.Parser        as SParse
#endif
#ifdef WITH_CLIKE_PARSER
import qualified Ohua.Compat.Clike.Lexer         as CLex
import qualified Ohua.Compat.Clike.Parser        as CParse
#endif

type LParser = L.ByteString -> (Maybe TyAnnMap, RawNamespace)

definedLangs :: [(String, String, LParser)]
definedLangs =
#ifdef WITH_SEXPR_PARSER
  ( ".ohuas"
  , "S-Expression frontend for the algorithm language"
  , (Nothing,) . SParse.parseNS . SLex.tokenize
  ) :
#endif
#ifdef WITH_CLIKE_PARSER
  ( ".ohuac"
  , "C/Rust-like frontent for the algorithm language"
  , let reNS :: Namespace (Annotated (FunAnn (TyExpr SomeBinding)) (Expr SomeBinding)) -> (Maybe TyAnnMap, RawNamespace)
        reNS ns = (Just $ HM.fromList anns, ns & decls .~ HM.fromList newDecls)
          where
            (anns, newDecls) = unzip $ map (\(name, Annotated tyAnn expr) -> ((name, tyAnn), (name, expr))) (HM.toList $ ns ^. decls)
        remMutAnn = decls . each . OLC.annotation %~ fmap (view OLC.value)
    in reNS . remMutAnn . CParse.parseNS . CLex.tokenize
  ) :
#endif
  []



getParser :: String -> L.ByteString -> (Maybe TyAnnMap, RawNamespace)
getParser ext | Just a <- find ((== ext) . view _1) definedLangs = a ^. _3
              | otherwise = error $ "No parser defined for files with extension '" ++ ext ++ "'"


type IFaceDefs = HM.HashMap QualifiedBinding Expression
type ModMap = HM.HashMap NSRef (MVar ResolvedNamespace)
type ModTracker = IORef ModMap
type RawNamespace = Namespace (Expr SomeBinding)
type ResolvedNamespace = Namespace Expression
type CompM = ExceptT Error (LoggingT IO)
type TyAnnMap = HM.HashMap Binding (FunAnn (TyExpr SomeBinding))


data GraphFile = GraphFile
  { graph          :: OutGraph
  , mainArity      :: Int
  , sfDependencies :: HS.HashSet QualifiedBinding
  } deriving (Eq, Show, Generic)


instance ToJSON GraphFile where toEncoding = genericToEncoding defaultOptions
instance FromJSON GraphFile where parseJSON = genericParseJSON defaultOptions


stdNamespace =
    ( nsRefFromList ["ohua", "lang"]
    , [ "id", "smap", "if" ] -- TODO complete list
    )


resolveNS :: forall m . MonadError Error m => IFaceDefs -> RawNamespace -> m ResolvedNamespace
resolveNS ifacem ns@(Namespace modname algoImports sfImports' decls) = do
  resDecls <- flip runReaderT (mempty, ifacem) $
                go0 (topSortDecls
                     (\case Unqual bnd | bnd `HS.member` locallyDefinedAlgos -> Just bnd
                            _ -> Nothing)
                     $ HM.toList decls)
  pure $ ns & NS.decls .~ HM.fromList resDecls
  where
    go0 [] = pure []
    go0 ((name, expr):xs) = do
        done <- go expr
        local (second $ HM.insert (QualifiedBinding modname name) done) $
             ((name, done) :) <$> (go0 xs)

    go :: Expr SomeBinding -> ReaderT (HS.HashSet Binding, IFaceDefs) m Expression
    go (Let assign val body) =
        registerAssign assign $ Let assign <$> go val <*> go body
    go (Var (Unqual bnd)) = do
        isLocal <- asks (HS.member bnd . fst)

        if isLocal
          then pure $ Var $ Local bnd
          else
            case (HM.lookup bnd algoRefers, HM.lookup bnd sfRefers) of
                (Just algo, Just sf) ->
                  throwError $ "Ambiguous ocurrence of unqualified binding " <> showS bnd
                                <> ". Could refer to algo " <> showS algo <> " or sf " <> showS sf
                (Just algoname, _) ->
                    maybe (throwError $ "Algo not loaded " <> showS algoname) pure
                      =<< asks (HM.lookup algoname . snd)
                (_, Just sf) -> pure $ Var $ Sf sf Nothing
                _ -> throwError $ "Binding not in scope " <> showS bnd
    go (Var (Qual qb)) = do
        algo <- asks (HM.lookup qb . snd)
        case algo of
          Just algo -> pure algo
          _ | qbNamespace qb `HS.member` importedSfNamespaces -> pure $ Var (Sf qb Nothing)
          _ -> throwError $ "No matching algo available or namespace not loaded for " <> showS qb
    go (Apply expr expr2) = Apply <$> go expr <*> go expr2
    go (Lambda assign body) =
        registerAssign assign $ Lambda assign <$> go body

    sfImports = stdNamespace : sfImports'

    registerAssign = local . first . HS.union . HS.fromList . flattenAssign

    locallyDefinedAlgos = HS.fromMap $ HM.map (const ()) decls

    importedSfNamespaces = HS.fromList $ map fst sfImports

    algoRefers = mkReferMap $ (modname, HM.keys decls) : algoImports
    sfRefers = mkReferMap sfImports

    mkReferMap importList = HM.fromListWith reportCollidingRef
        [ (shortname, QualifiedBinding sourceNS shortname)
        | (sourceNS, referList) <- importList
        , shortname <- referList
        ]

    reportCollidingRef a b =
        error $ "Colliding refer for '" <> show a <> "' and '" <> show b <> "' in " <> show modname


readAndParse :: MonadIO m => String -> m (Maybe TyAnnMap, RawNamespace)
readAndParse filename = getParser (takeExtension filename) <$> liftIO (L.readFile filename)


gatherDeps :: IORef ModMap -> Namespace a -> CompM IFaceDefs
gatherDeps tracker ns = do
    mods <- mapConcurrently (registerAndLoad tracker) (map fst $ ns ^. algoImports)
    pure $ HM.fromList
        [ (QualifiedBinding (ns ^. NS.name) name, algo)
        | ns <- mods
        , (name, algo) <- HM.toList $ ns ^. decls
        ]


findSourceFile :: NSRef -> CompM String
findSourceFile modname = do
    candidates <- filterM (liftIO . doesFileExist) $ map (asFile <.>) extensions
    case candidates of
        [] -> throwError $ "No file found for module " <> showS modname
        [f] -> pure f
        files -> throwError $ "Found multiple files matching " <> showS modname <> ": " <> showS files
  where
    asFile = intercalate "/" $ map (Str.toString . unBinding) $ nsRefToList modname
    extensions = map (^. _1) definedLangs


loadModule :: ModTracker -> NSRef -> CompM ResolvedNamespace
loadModule tracker modname = do
    filename <- findSourceFile modname
    (anns, rawMod) <- readAndParse filename
    unless (rawMod ^. name == modname) $
        throwError $ "Expected module with name " <> Str.showS modname <> " but got " <> Str.showS (rawMod ^. name)
    loadDepsAndResolve tracker rawMod


loadDepsAndResolve :: ModTracker -> RawNamespace -> CompM ResolvedNamespace
loadDepsAndResolve tracker rawMod = flip resolveNS rawMod =<< gatherDeps tracker rawMod


registerAndLoad :: ModTracker -> NSRef -> CompM ResolvedNamespace
registerAndLoad tracker mod = registerAnd tracker mod (loadModule tracker mod)


registerAnd :: (Eq ref, Hashable ref) => IORef (HM.HashMap ref (MVar load)) -> ref -> CompM load -> CompM load
registerAnd tracker mod ac = do
    newModRef <- newEmptyMVar
    actualRef <- atomicModifyIORef' tracker $ \map ->
        case map ^? ix mod of
            Just mvar -> (map, Left mvar)
            Nothing   -> (HM.insert mod newModRef map, Right newModRef)
    case actualRef of
        Left toWait -> readMVar toWait
        Right build -> do
            compiled <- ac
            putMVar build compiled
            pure compiled


gatherSFDeps :: Expression -> HS.HashSet QualifiedBinding
gatherSFDeps = cata $ \case
  VarF (Sf ref _) -> HS.singleton ref
  other -> fold other


topSortMods :: [Namespace ResolvedSymbol] -> [Namespace ResolvedSymbol]
topSortMods = topSortWith (^. name) (map fst . view algoImports)


topSortWith :: (Hashable b, Eq b) => (a -> b) -> (a -> [b]) -> [a] -> [a]
topSortWith getIdent getDeps mods' = concat @[] $ ana (uncurry go) (mempty, mods')
  where
    go satisfied avail
      | null newSat =
        if null newAvail
        then Nil
        else error "Unsortable! (Probably due to a cycle)"
      | otherwise = Cons newSat $ (HS.union (HS.fromList (map getIdent newSat)) satisfied, newAvail)
      where
        (newSat, newAvail) = partition (all (`HS.member` satisfied) . getDeps) avail


unlessM :: Monad m => m Bool -> m () -> m ()
unlessM cond a = cond >>= \b -> unless b a


topSortDecls :: (a -> Maybe Binding) -> [(Binding, Expr a)] -> [(Binding, Expr a)]
topSortDecls f decls = map fst $ topSortWith (fst . fst) snd declsWDeps
  where
    localAlgos = HS.fromList $ map fst decls
    getDeps e = HS.toList $ snd $ evalRWS (go e) mempty ()
      where
        go = cata $ \case
          LetF assign val body -> local (HS.union $ HS.fromList $ flattenAssign assign) $ val >> body
          VarF thing | Just bnd <- f thing -> unlessM (asks $ HS.member bnd) $ when (bnd `HS.member` localAlgos) $ tell [bnd]
          LambdaF assign body -> local (HS.union $ HS.fromList $ flattenAssign assign) body
          e -> sequence_ e

    declsWDeps = zip decls $ map (getDeps . snd) decls


mainToEnv :: Expression -> (Int, Expression)
mainToEnv = go 0 id
  where
    go !i f (Lambda assign body) = go (i+1) (f . Let assign (Var $ Env $ HostExpr i)) body
    go !i f rest = (i, f rest)

formatRustType :: TyExpr SomeBinding -> String
formatRustType = go []
  where
    formatRef sb = concat $ intersperse "::" (map (Str.toString . unBinding) $ bnds)
      where
        bnds = case sb of
                 Unqual b                       -> [b]
                 Qual (QualifiedBinding ns bnd) -> nsRefToList ns ++ [bnd]

    go l (TyRef ref) = formatRef ref ++
      if null l
      then ""
      else "<" ++ intercalate "," l ++ ">"
    go l (TyApp t1 t2) = go (formatRustType t2:l) t1

data Command
  = Build
  | DumpType DumpOpts

type LangFormatter = TyExpr SomeBinding -> String

langs :: [(String, LangFormatter)]
langs =
  [("rust", formatRustType)]

data DumpOpts = DumpOpts
  { dumpLang :: LangFormatter
  }

data CmdOpts = CmdOpts
    { command_        :: Command
    , inputModuleFile :: FilePath
    , entrypoint      :: Str.Str
    , outputPath      :: Maybe FilePath
    }


runCompM :: CompM () -> IO ()
runCompM c = runStderrLoggingT $ runExceptT c >>= either (logErrorN . T.pack . Str.toString) pure


main :: IO ()
main = runCompM $ do
    opts@CmdOpts { inputModuleFile = inputModFile, outputPath = out, entrypoint } <- liftIO $ execParser odef

    modTracker <- newIORef HM.empty

    (mainAnns, rawMainMod) <- readAndParse inputModFile

    case command_ opts of
      DumpType (DumpOpts format) ->
        case mainAnns of
          Nothing -> throwError "No annotations present for the module"
          Just m ->
            case m ^? ix (Binding entrypoint) of
              Nothing -> throwError "Could not find chosen main module"
              Just (FunAnn args ret) ->
                liftIO $ L.writeFile (fromMaybe (inputModFile -<.> "type-dump") out) $ encode $ object
                  [ "arguments" A..= map format args
                  , "return" A..= format ret
                  ]
      Build -> do
        mainMod <- registerAnd modTracker (rawMainMod ^. name) $ loadDepsAndResolve modTracker rawMainMod

        case mainMod ^? decls . ix (Binding entrypoint) of
          Nothing -> throwError $ "Module does not define specified entry point '" <> entrypoint <> "'"
          Just expr -> do

            let sfDeps = gatherSFDeps expr

            let (mainArity, completeExpr) = mainToEnv expr

            gr <- compile def def completeExpr
            liftIO $ L.writeFile (fromMaybe (inputModFile -<.> "ohuao") out) $ encode $ GraphFile
              { graph = gr
              , mainArity = mainArity
              , sfDependencies = sfDeps
              }
  where
    odef = info
        (helper <*> optsParser)
        ( fullDesc
        <> header "ohuac ~ the ohua standalone compiler"
        <> progDesc ("Compiles algorithm source files into a dataflow graph, which can be read and executed by a runtime. Supported module file extensions are: "
            <> intercalate ", " (map (\a -> "'" <> a ^. _1 <> "'") definedLangs)
            )
        )
    dumpOpts = DumpOpts
      <$> argument (maybeReader $ flip lookup langs . map C.toLower)
        (  metavar "LANG"
        <> help "Language format for the types"
        )
    optsParser = CmdOpts
        <$> hsubparser
          (  command "build" (info (pure Build) (progDesc "Build the ohua graph"))
          <> command "dump-main-type" (info (DumpType <$> dumpOpts) (progDesc "Dump the type of the main function"))
          )
        <*> argument str
            (  metavar "SOURCE"
            <> help "Source file to compile"
            )
        <*> argument (Str.fromString <$> str)
            (  metavar "MAIN"
            <> help "Algorithm that serves as entry point"
            <> value "main"
            )
        <*> optional
            (  strOption
            $  long "output"
            <> metavar "PATH"
            <> short 'o'
            <> help "Path to write the output to (default: input filename with '.ohuao' extension for 'build' and '.type-dump' for 'dump-main-type')"
            )

