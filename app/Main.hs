{-# LANGUAGE TemplateHaskell #-}
module Main where

import Ohua.Prelude

import Data.Aeson as A
import qualified Data.ByteString.Lazy.Char8 as L (writeFile)
import qualified Data.Char as C (toLower)
import qualified Data.HashSet as HS (fromList, member, HashSet)
import Data.List (intercalate, lookup)
import qualified Data.String as Str
import Language.Haskell.TH
import Lens.Micro.Internal (Index, IxValue, Ixed, ix)
import Options.Applicative as O
import Options.Applicative.Help.Pretty as O
import System.Directory (createDirectoryIfMissing)
import qualified System.FilePath as FP ((-<.>), takeDirectory)

import Ohua.ALang.NS
import Ohua.CodeGen.Iface
import qualified Ohua.CodeGen.JSONObject as JSONGen
import qualified Ohua.CodeGen.SimpleJavaClass as JavaGen
import Ohua.Compile
import Ohua.Standalone
import Ohua.Stage (knownStages)
import Ohua.Stdlib (stdlib)
import Ohua.Unit

newtype DumpOpts = DumpOpts
    { dumpLang :: LangFormatter
    }

data BuildOpts = BuildOpts
    { outputFormat :: CodeGenSelection
    , useStdlib :: Bool
    , stageHandlingOpt :: StageHandling
    , extraFeatures :: HS.HashSet Feature
    }

data Command
    = Build BuildOpts
    | DumpType DumpOpts

data CmdOpts = CmdOpts
    { command_ :: Command
    , inputModuleFile :: Text
    , entrypoint :: Binding
    , outputPath :: Maybe Text
    , logLevel :: LogLevel
    }

data CodeGenSelection
    = JsonGraph
    | SimpleJavaClass
    deriving (Read, Show, Bounded, Enum)

selectionToGen :: CodeGenSelection -> CodeGen
selectionToGen SimpleJavaClass = JavaGen.generate
selectionToGen JsonGraph = JSONGen.generate

-- The following splice generates the following two conversions from the
-- 'codeGenStrings' list
--
-- readCodeGen :: (IsString s, IsString err, Eq s) => s -> Either err CodeGenSelection
-- showCodeGen :: IsString s => CodeGenSelection -> s
$(let codeGenStrings =
          [('JsonGraph, "json-graph"), ('SimpleJavaClass, "simple-java-class")]
      (readClauses, showClauses) =
          unzip
              [ ( Clause
                      [LitP $ StringL strRep]
                      (NormalB $ ConE 'Right `AppE` ConE constr)
                      []
                , Clause [ConP constr []] (NormalB $ LitE $ StringL strRep) [])
              | (constr, strRep) <- codeGenStrings
              ]
      showN = mkName "showCodeGen"
      readN = mkName "readCodeGen"
      strVar = mkName "str"
      errMgs =
          "Unrecognized code gen type. Valid options: " ++
          intercalate ", " (map snd codeGenStrings)
      varIsStr var = ConT ''IsString `AppT` VarT var
      strVarIsString = varIsStr strVar
      errVar = mkName "err"
   in pure
          [ SigD showN $
            ForallT [PlainTV strVar] [strVarIsString] $
            ArrowT `AppT` ConT ''CodeGenSelection `AppT` VarT strVar
          , FunD showN showClauses
          , SigD readN $
            ForallT
                [PlainTV strVar, PlainTV errVar]
                [strVarIsString, ConT ''Eq `AppT` VarT strVar, varIsStr errVar] $
            ArrowT `AppT` VarT strVar `AppT`
            (ConT ''Either `AppT` VarT errVar `AppT` ConT ''CodeGenSelection)
          , FunD
                readN
                (readClauses ++
                 [ Clause
                       [WildP]
                       (NormalB $ ConE 'Left `AppE` LitE (StringL errMgs))
                       []
                 ])
          ])

(-<.>) :: Text -> Text -> Text
p1 -<.> p2 = toText $ toString p1 FP.-<.> toString p2

runCompM :: LogLevel -> CompM () -> IO ()
runCompM targetLevel c =
    runStderrLoggingT $
    filterLogger (\_ level -> level >= targetLevel) $
    runExceptT c >>= either exitError pure
  where
    exitError message = do
        logErrorN message
        exitFailure

main :: IO ()
main = do
    opts@CmdOpts { inputModuleFile = inputModFile
                 , outputPath = out
                 , entrypoint
                 , logLevel
                 } <- execParser odef
    runCompM logLevel $ do
        modTracker <- newIORef mempty
        (mainAnns, rawMainMod) <- readAndParse inputModFile
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
                        let outPath =
                                fromMaybe (inputModFile -<.> "type-dump") out
                        liftIO $
                            L.writeFile (toString outPath) $
                            encode $
                            object
                                [ "arguments" A..= map format args
                                , "return" A..= format ret
                                ]
                        logInfoN $
                            "Wrote a type dump of '" <> unwrap entrypoint <>
                            "' from '" <>
                            inputModFile <>
                            "' to '" <>
                            outPath <>
                            "'"
            Build BuildOpts { outputFormat
                            , useStdlib
                            , stageHandlingOpt
                            , extraFeatures
                            } -> do
                when useStdlib $ void $ insertDirectly modTracker stdlib
                mainMod <-
                    registerAnd modTracker (rawMainMod ^. name) $
                    loadDepsAndResolve modTracker rawMainMod
                expr <- getMain $ mainMod ^. decls
                let sfDeps = gatherSFDeps expr
                let (mainArity, completeExpr) = mainToEnv expr
                gr <-
                    compile
                        (def & stageHandling .~ stageHandlingOpt &
                         transformRecursiveFunctions .~
                         ("tail-recursion" `elem` extraFeatures))
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
                let outputPath = fromMaybe (nameSuggest) out
                liftIO $
                    createDirectoryIfMissing
                        True
                        (FP.takeDirectory $ toString outputPath)
                liftIO $ L.writeFile (toString outputPath) code
                logInfoN $
                    "Compiled '" <> unwrap entrypoint <> "' from '" <>
                    inputModFile <>
                    "' to " <>
                    showCodeGen outputFormat
                logInfoN $ "Code written to '" <> outputPath <> "'"
  where
    odef =
        info
            (helper <*> optsParser)
            (fullDesc <> header "ohuac ~ the ohua standalone compiler" <>
             progDescDoc
                 (Just $
                  softStr
                      "Compiles algorithm source files into a dataflow graph, which can be read and executed by a runtime." <$$>
                  "Supported module file extensions are:" </>
                  fillSep
                      (punctuate comma $
                       map (squotes . text . toString . view _1) definedLangs)))
    dumpOpts =
        DumpOpts <$>
        argument
            (maybeReader $ flip lookup langs . toText . map C.toLower)
            (metavar "LANG" <> help "Language format for the types")
    buildOpts =
        BuildOpts <$>
        O.option
            (eitherReader readCodeGen)
            (O.value JsonGraph <>
             helpDoc
                 (Just $
                  softStr "Format to emit the generated code in." <//>
                  "Accepted choices:" <+>
                  fillSep
                      (punctuate
                           comma
                           (map (text . showCodeGen)
                                [(minBound :: CodeGenSelection) ..])) </>
                  "(default: json-graph)") <>
             long "code-gen" <>
             short 'g') <*>
        O.switch
            (long "with-stdlib" <>
             help
                 "Link the `ohua.std` namespace of higher order functions into the program. (experimental)") <*>
        ((\stopOn dumpStages sname ->
              ( if sname `HS.member` HS.fromList dumpStages
                    then DumpPretty
                    else Don'tDump
              , stopOn == Just sname)) <$>
         optional
             (O.strOption $
              long "stop-on" <> help "Stop execution after this stage." <>
              metavar "STAGE") <*>
         many
             (O.strOption
                  (long "dump-stage" <>
                   help
                       "Dump the code at this stage. (can be supplied multiple times) The code is dumped to a file called <stage-name>.dump" <>
                   metavar "STAGE"))) <*>
        (HS.fromList <$>
         many
             (strOption
                  (short 'f' <> long "feature" <>
                   help "Enable extra (experimental) features")))
    softStr = fillSep . map text . Str.words
    optsParser =
        CmdOpts <$>
        hsubparser
            (command
                 "build"
                 (info
                      (Build <$> buildOpts)
                      (progDescDoc $
                       Just $
                       "Build the ohua graph. " <$$> "" <$$>
                       softStr
                           "The options --dump-stage and --stop-on pertain to stages. See https://ohua.rtfd.io/en/latest/debugging.html#stages." <$$>
                       fillSep
                           ("I know about the following stages:" :
                            punctuate comma (map (text . toString) knownStages)))) <>
             command
                 "dump-main-type"
                 (info
                      (DumpType <$> dumpOpts)
                      (progDesc "Dump the type of the main function"))) <*>
        argument str (metavar "SOURCE" <> help "Source file to compile") <*>
        argument
            (eitherReader $ mapLeft toString . make . toText)
            (metavar "MAIN" <> help "Algorithm that serves as entry point" <>
             O.value "main") <*>
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
