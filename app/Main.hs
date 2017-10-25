{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE CPP               #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies      #-}
module Main where


import           Control.Arrow
import           Control.Concurrent.Async
import           Control.Concurrent.MVar
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Reader
import           Control.Monad.RWS
import           Control.Monad.Writer
import           Data.Aeson
import qualified Data.ByteString.Lazy.Char8 as L
import           Data.Foldable
import           Data.Hashable
import qualified Data.HashMap.Strict        as HM
import qualified Data.HashSet               as HS
import           Data.IORef
import           Data.List                  (partition)
import           Data.Maybe
import           Data.Monoid
import           Data.String                (fromString)
import qualified Data.Text                  as T
import qualified Data.Text.IO               as T
import           GHC.Generics
import           Ohua.ALang.Lang
import           Ohua.ALang.NS
import           Ohua.Compile
import           Ohua.DFGraph
import           Ohua.Serialize.JSON
import           Ohua.Types
import           Options.Applicative
import           System.Directory
import           System.Environment
import           System.FilePath            (takeExtension, (-<.>), (<.>))
import           Data.List (intercalate)

#ifdef WITH_SEXPR_PARSER
import qualified Ohua.Compat.SExpr.Lexer    as SLex
import qualified Ohua.Compat.SExpr.Parser   as SParse
#endif
#ifdef WITH_CLIKE_PARSER
import qualified Ohua.Compat.Clike.Lexer    as CLex
import qualified Ohua.Compat.Clike.Parser   as CParse
#endif


getParser :: String -> L.ByteString -> RawNamespace
#ifdef WITH_SEXPR_PARSER
getParser ".ohuas" = SParse.parseNS . SLex.tokenize
#endif
#ifdef WITH_CLIKE_PARSER
getParser ".ohuac" = CParse.parseNS . CLex.tokenize
#endif
getParser ext = error $ "No parser defined for files with extension '" ++ ext ++ "'"

supportedExtensions :: [(String, String)]
supportedExtensions =     
#ifdef WITH_SEXPR_PARSER
        (".ohuas", "S-Expression frontend for the algorithm language") :
#endif
#ifdef WITH_CLIKE_PARSER
        (".ohuac", "C/Rust-like frontent for the algorithm language") :
#endif
        []

type IFaceDefs = HM.HashMap QualifiedBinding Expression
type ModMap = HM.HashMap NSRef (MVar (Namespace ResolvedSymbol))
type ModTracker = IORef ModMap
type RawNamespace = Namespace SomeBinding
type ResolvedNamespace = Namespace ResolvedSymbol


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


resolveNS :: IFaceDefs -> RawNamespace -> ResolvedNamespace
resolveNS ifacem ns@(Namespace modname algoImports sfImports' decls) =
    ns { nsDecls = HM.fromList resDecls }
  where
    resDecls = flip runReader (mempty, ifacem) $
        go0 (topSortDecls
                (\case Unqual bnd | bnd `HS.member` locallyDefinedAlgos -> Just bnd ; _ -> Nothing)
                $ HM.toList decls)

    go0 [] = pure []
    go0 ((name, expr):xs) = do
        done <- go expr
        local (second $ HM.insert (QualifiedBinding modname name) done) $
             ((name, done) :) <$> (go0 xs)

    go :: Expr SomeBinding -> Reader (HS.HashSet Binding, IFaceDefs) Expression
    go (Let assign val body) =
        registerAssign assign $ Let assign <$> go val <*> go body
    go (Var (Unqual bnd)) = do
        isLocal <- asks (HS.member bnd . fst)

        if isLocal then
            pure $ Var $ Local bnd
        else
            case (HM.lookup bnd algoRefers, HM.lookup bnd sfRefers) of
                (Just algo, Just sf) ->
                  error $ "Ambiguous ocurrence of unqualified binding " ++ show bnd
                    ++ ". Could refer to algo " ++ show algo ++ " or sf " ++ show sf
                (Just algoname, _) ->
                    fromMaybe (error $ "Algo not loaded " ++ show algoname)
                      <$> asks (HM.lookup algoname . snd)
                (_, Just sf) -> pure $ Var $ Sf sf Nothing
                _ -> error $ "Binding not in scope " ++ show bnd
    go (Var (Qual qb)) = do
        algo <- asks (HM.lookup qb . snd)
        pure $
            case algo of
                Just algo -> algo
                _ | qbNamespace qb `HS.member` importedSfNamespaces -> Var (Sf qb Nothing)
                _ -> error $ "No matching algo available or namespace not loaded for " ++ show qb
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
        error $ "Colliding refer for '" ++ show a ++ "' and '" ++ show b ++ "' in " ++ show modname


readAndParse :: String -> IO RawNamespace
readAndParse filename = getParser (takeExtension filename) <$> L.readFile filename


gatherDeps :: IORef ModMap -> Namespace a -> IO IFaceDefs
gatherDeps tracker Namespace{ nsAlgoImports=algoImports } = do
    mods <- mapConcurrently (registerAndLoad tracker) (map fst algoImports)
    pure $ HM.fromList
        [ (QualifiedBinding (nsName ns) name, algo)
        | ns <- mods
        , (name, algo) <- HM.toList $ nsDecls ns
        ]


findSourceFile :: NSRef -> IO String
findSourceFile modname = do
    candidates <- filterM doesFileExist $ map (asFile <.>) extensions
    case candidates of
        [] -> error $ "No file found for module " ++ show modname
        [f] -> pure f
        files -> error $ "Found multiple files matching " ++ show modname ++ ": " ++ show files
  where
    asFile = T.unpack $ T.intercalate "/" $ map unBinding $ nsRefToList modname
    extensions = map fst supportedExtensions


loadModule :: ModTracker -> NSRef -> IO ResolvedNamespace
loadModule tracker modname = do
    filename <- findSourceFile modname
    rawMod <- readAndParse filename
    unless (nsName rawMod == modname) $
        error $ "Expected module with name " ++ show modname ++ " but got " ++ show (nsName rawMod)
    loadDepsAndResolve tracker rawMod


loadDepsAndResolve :: ModTracker -> RawNamespace -> IO ResolvedNamespace
loadDepsAndResolve tracker rawMod = flip resolveNS rawMod <$> gatherDeps tracker rawMod


registerAndLoad :: ModTracker -> NSRef -> IO ResolvedNamespace
registerAndLoad tracker mod = registerAnd tracker mod (loadModule tracker mod)


registerAnd :: ModTracker -> NSRef -> IO ResolvedNamespace -> IO ResolvedNamespace
registerAnd tracker mod ac = do
    newModRef <- newEmptyMVar
    actualRef <- atomicModifyIORef' tracker $ \map ->
        case HM.lookup mod map of
            Just mvar -> (map, Left mvar)
            Nothing   -> (HM.insert mod newModRef map, Right newModRef)
    case actualRef of
        Left toWait -> readMVar toWait
        Right build -> do
            compiled <- ac
            putMVar build compiled
            pure compiled


gatherSFDeps :: Expression -> HS.HashSet QualifiedBinding
gatherSFDeps = execWriter . foldlExprM (const . go) ()
  where
    go (Var (Sf name _)) = tell [name]
    go _                 = pure ()


topSortMods :: [Namespace ResolvedSymbol] -> [Namespace ResolvedSymbol]
topSortMods = topSortWith nsName (map fst . nsAlgoImports)


topSortWith :: (Hashable b, Eq b) => (a -> b) -> (a -> [b]) -> [a] -> [a]
topSortWith getIdent getDeps mods' = snd $ evalRWS go (mempty, mods') ()
  where
    go = do
        (satisfied, avail) <- ask
        let (newSat, newAvail) = partition (all (`HS.member` satisfied) . getDeps) avail
        if null newSat then
            unless (null newAvail) $ error "Unsortable! (Probably due to a cycle)"
        else do
            tell newSat
            local (HS.union (HS.fromList $ map getIdent newSat) *** const newAvail) go


topSortDecls :: (a -> Maybe Binding) -> [(Binding, Expr a)] -> [(Binding, Expr a)]
topSortDecls f decls = map fst $ topSortWith (fst . fst) snd declsWDeps
  where
    localAlgos = HS.fromList $ map fst decls
    getDeps e = HS.toList $ snd $ evalRWS (go e) mempty ()
      where
        go (Let assign val body) =
          local (HS.union $ HS.fromList $ flattenAssign assign) $ go val >> go body
        go (Var thing) | Just bnd <- f thing = do
            isLocal <- asks (HS.member bnd)
            if isLocal then
                pure ()
            else
                when (bnd `HS.member` localAlgos) $ tell [bnd]
        go (Var _) = pure ()
        go (Lambda assign body) = local (HS.union $ HS.fromList $ flattenAssign assign) $ go body
        go (Apply function val) = go function >> go val

    declsWDeps = zip decls $ map (getDeps . snd) decls


mainToEnv :: Expression -> (Int, Expression)
mainToEnv = go 0 id
  where
    go !i f (Lambda assign body) = go (i+1) (f . Let assign (Var $ Env $ HostExpr i)) body
    go !i f rest = (i, f rest)


data CmdOpts = CmdOpts
    { inputModuleFile :: FilePath
    , outputPath :: Maybe FilePath
    }


main :: IO ()
main = do
    CmdOpts { inputModuleFile = inputModFile, outputPath = out } <- execParser odef

    modTracker <- newIORef HM.empty

    rawMainMod <- readAndParse inputModFile

    mainMod <- registerAnd modTracker (nsName rawMainMod) $ loadDepsAndResolve modTracker rawMainMod

    case HM.lookup "main" $ nsDecls mainMod of
        Nothing -> error "Main module has no main function"
        Just expr -> do

            let sfDeps = gatherSFDeps expr

            let (mainArity, completeExpr) = mainToEnv expr

            case compile completeExpr of
                Left err -> do
                    T.putStrLn err
                    print completeExpr
                Right gr -> do
                    L.writeFile (fromMaybe (inputModFile -<.> "ohuao") out) $ encode $ GraphFile
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
            <> intercalate ", " (map (\a -> "'" <> fst a <> "'") supportedExtensions)
            )
        )
    optsParser = CmdOpts
        <$> argument str
            (  metavar "SOURCE"
            <> help "Source file to compile"
            )
        <*> optional 
            (  strOption
            $  long "output"
            <> metavar "PATH"
            <> short 'o'
            <> help "Path to write the output to (default: input filename with '.ohuao' extension)"
            )
