module Main where

import Protolude

import Data.Aeson as A
import qualified Data.ByteString.Lazy.Char8 as L
import qualified Data.Char as C
import Data.Default.Class
import Data.IORef
import Data.List (lookup)
import Lens.Micro
import Lens.Micro.Internal (Index, IxValue, Ixed)
import Options.Applicative as O
import System.FilePath ((-<.>), takeDirectory)
import System.Directory (createDirectoryIfMissing)
import qualified System.Exit.Codes as EX

import Ohua.ALang.NS
import Ohua.Compile
import Ohua.Monad
import Ohua.Standalone
import Ohua.Types
import qualified Ohua.CodeGen.JSONObject as JSONGen
import qualified Ohua.CodeGen.SimpleJavaClass as JavaGen
import Ohua.CodeGen.Iface
import Ohua.Unit
import Ohua.Util (mapLeft)

newtype DumpOpts = DumpOpts
    { dumpLang :: LangFormatter
    }

data CmdOpts = CmdOpts
    { command_ :: Command
    , inputModuleFile :: FilePath
    , entrypoint :: Binding
    , outputPath :: Maybe FilePath
    , logLevel :: LogLevel
    }

data CodeGenSelection
    = GenJsonObject
    | GenSimpleJavaClass
    deriving (Read, Show, Bounded, Enum)

selectionToGen :: CodeGenSelection -> CodeGen
selectionToGen GenSimpleJavaClass = JavaGen.generate
selectionToGen GenJsonObject = JSONGen.generate

newtype BuildOpts = BuildOpts
    { outputFormat :: CodeGenSelection
    }

data Command
  = Build BuildOpts
  | DumpType DumpOpts


genTypes :: [Char] -> CodeGen
genTypes "json-object" = JSONGen.generate
genTypes "simple-java-class" = JavaGen.generate
genTypes t = panic $ "Unsupported code gen type " <> toS t

runCompM :: LogLevel -> CompM () -> IO ()
runCompM targetLevel c =
    runStderrLoggingT $
    filterLogger (\_ level -> level >= targetLevel) $
    runExceptT c >>= either exitError pure
  where
    exitError message = do
        logErrorN $ toS message
        liftIO $ exitWith EX.codeSoftware

main :: IO ()
main = do
    opts@CmdOpts { inputModuleFile = inputModFile
                 , outputPath = out
                 , entrypoint
                 , logLevel
                 } <- execParser odef
    runCompM logLevel $ do
        modTracker <- liftIO $ newIORef mempty
        (mainAnns, rawMainMod) <- readAndParse $ toS inputModFile
        let getMain ::
                   (Ixed m, Index m ~ Binding, MonadError Error mo)
                => m
                -> mo (IxValue m)
            getMain m =
                case m ^? ix entrypoint of
                    Nothing ->
                        throwError $
                        "Module does not define specified entry point '" <>
                        unwrap entrypoint <>
                        "'"
                    Just x -> pure x
        case command_ opts of
            DumpType (DumpOpts format) ->
                case mainAnns of
                    Nothing ->
                        throwError "No annotations present for the module"
                    Just m -> do
                        FunAnn args ret <- getMain m
                        liftIO $
                            L.writeFile
                                (fromMaybe (inputModFile -<.> "type-dump") out) $
                            encode $
                            object
                                [ "arguments" A..= map format args
                                , "return" A..= format ret
                                ]
            Build BuildOpts {outputFormat} -> do
                mainMod <-
                    registerAnd modTracker (rawMainMod ^. name) $
                    loadDepsAndResolve modTracker rawMainMod
                expr <- getMain $ mainMod ^. decls
                let sfDeps = gatherSFDeps expr
                let (mainArity, completeExpr) = mainToEnv expr
                gr <-
                    compile
                        def
                        (def {passAfterDFLowering = cleanUnits})
                        completeExpr
                (nameSuggest, code) <-
                    flip runReaderT CodeGenOpts $
                    selectionToGen
                        outputFormat
                        CodeGenData
                            { graph = gr
                            , entryPointArity = mainArity
                            , sfDependencies = sfDeps
                            , annotations = mainAnns
                            , entryPointName = entrypoint
                            , entryPointNamespace = rawMainMod ^. name
                            }
                let outputPath = fromMaybe (toS nameSuggest) out
                liftIO $
                    createDirectoryIfMissing True (takeDirectory outputPath)
                liftIO $ L.writeFile outputPath code
  where
    odef =
        info
            (helper <*> optsParser)
            (fullDesc <> header "ohuac ~ the ohua standalone compiler" <>
             progDesc
                 ("Compiles algorithm source files into a dataflow graph, which can be read and executed by a runtime. Supported module file extensions are: " <>
                  intercalate
                      ", "
                      (map (\a -> toS $ "'" <> a ^. _1 <> "'") definedLangs)))
    dumpOpts =
        DumpOpts <$>
        argument
            (maybeReader $ flip lookup langs . toS . map C.toLower)
            (metavar "LANG" <> help "Language format for the types")
    buildOpts =
        BuildOpts <$>
        O.option
            auto
            (value GenJsonObject <>
             help
                 ("Format to emit the generated code in. Accepted choices: " <>
                  intercalate
                      ", "
                      (map show [(minBound :: CodeGenSelection) ..])) <>
             long "format" <>
             short 'f' <>
             showDefault)
    optsParser =
        CmdOpts <$>
        hsubparser
            (command
                 "build"
                 (info (Build <$> buildOpts) (progDesc "Build the ohua graph")) <>
             command
                 "dump-main-type"
                 (info
                      (DumpType <$> dumpOpts)
                      (progDesc "Dump the type of the main function"))) <*>
        argument str (metavar "SOURCE" <> help "Source file to compile") <*>
        argument
            (eitherReader $ mapLeft toS . make . toS)
            (metavar "MAIN" <> help "Algorithm that serves as entry point" <>
             value "main") <*>
        optional
            (strOption $
             long "output" <> metavar "PATH" <> short 'o' <>
             help
                 "Path to write the output to (default: input filename with '.ohuao' extension for 'build' with the JSON format and '.java' with the java format and '.type-dump' for 'dump-main-type')") <*>
        ((\verbose debug ->
              if debug
                  then LevelDebug
                  else if verbose
                           then LevelInfo
                           else LevelWarn) <$>
         switch
             (short 'v' <> long "verbose" <>
              help "Print more detailed logging messages") <*>
         switch
             (long "debug" <>
              help "Activate all logging messages for debugging purposes."))
