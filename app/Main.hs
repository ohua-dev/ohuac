{-# LANGUAGE TemplateHaskell, CPP, ImplicitParams #-}

module Main where

import Ohua.Prelude

import Control.Category ((>>>))
import Control.Lens (Index, IxValue, Ixed, (^?), (^?!), _Just, ix, view)
import Data.Aeson as A
import qualified Data.ByteString.Lazy.Char8 as L (writeFile)
import qualified Data.Char as C (toLower)
import qualified Data.Functor.Foldable as RS
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS (HashSet, fromList, member)
import qualified Data.IntMap as IM
import Data.List (intercalate, lookup)
import qualified Data.String as Str
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Time as Time
import Data.Traversable (for)
import Language.Haskell.TH
import Ohua.ALang.Lang (Expr(Lambda))
import Options.Applicative as O
import Options.Applicative.Help.Pretty as O
import qualified Prelude
import System.Directory (createDirectoryIfMissing)
import qualified System.FilePath as FP

import Ohua.ALang.PPrint ()
import Ohua.CodeGen.Iface
import qualified Ohua.CodeGen.JSONObject as JSONGen
import qualified Ohua.CodeGen.NoriaUDF as NoriaUDFGen
import qualified Ohua.CodeGen.SimpleJavaClass as JavaGen
import Ohua.Compile
import Ohua.Compile.Configuration
import Ohua.Frontend.NS
import Ohua.Stage (knownStages)
import Ohua.Standalone
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
    , sandbox :: Bool
    }

data Command
    = Build CommonCmdOpts
            BuildOpts
    | DumpType CommonCmdOpts
               DumpOpts
    | ShowVersion

data CommonCmdOpts = CommonCmdOpts
    { inputModuleFile :: Text
    , entrypoint :: Binding
    , outputPath :: Maybe Text
    , logLevel :: LogLevel
    }

data CodeGenSelection
    = JsonGraph
    | SimpleJavaClass
    | NoriaUDF
    deriving (Read, Show, Bounded, Enum, Eq)

-- The following splice generates the following two conversions from the
-- 'codeGenStrings' list
--
-- readCodeGen :: (IsString s, IsString err, Eq s) => s -> Either err CodeGenSelection
-- showCodeGen :: IsString s => CodeGenSelection -> s
$(let codeGenStrings =
          [ ('JsonGraph, "json-graph")
          , ('SimpleJavaClass, "simple-java-class")
          , ('NoriaUDF, "noria-udf")
          ]
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
          [ SigD showN $ ForallT [PlainTV strVar] [strVarIsString] $ ArrowT `AppT`
            ConT ''CodeGenSelection `AppT`
            VarT strVar
          , FunD showN showClauses
          , SigD readN $
            ForallT
                [PlainTV strVar, PlainTV errVar]
                [strVarIsString, ConT ''Eq `AppT` VarT strVar, varIsStr errVar] $
            ArrowT `AppT`
            VarT strVar `AppT`
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

runCompM :: LogLevel -> ExceptT Text (LoggingT IO) a -> IO a
runCompM targetLevel c =
    runStderrLoggingT $ filterLogger (\_ level -> level >= targetLevel) $
    runExceptT c >>=
    either exitError pure
  where
    exitError message = do
        logErrorN message
        exitFailure

main :: IO ()
main = do
    opts <- execParser odef
    case opts of
        ShowVersion -> do
            putStrLn ("ohuac v" <> CURRENT_PACKAGE_VERSION :: Text)
            putStrLn
                ("Compiled at " <>
                 $(do t <- liftIO Time.getCurrentTime
                      tz <- liftIO Time.getCurrentTimeZone
                      pure $ LitE $ StringL $ show t <> " (" <>
                          show (Time.localTimeOfDay $ Time.utcToLocalTime tz t) <>
                          " local)") :: Text)
        DumpType common@CommonCmdOpts {..} (DumpOpts format) ->
            withCommonSetup common $ \_ mainAnns _ getMain ->
                case mainAnns of
                    Nothing ->
                        throwError "No annotations present for the module"
                    Just m -> do
                        FunAnn args ret <- getMain m
                        let outPath =
                                fromMaybe
                                    (inputModuleFile -<.> "type-dump")
                                    outputPath
                        liftIO $ L.writeFile (toString outPath) $ encode $
                            object
                                [ "arguments" A..= map format args
                                , "return" A..= format ret
                                ]
                        logInfoN $ "Wrote a type dump of '" <> unwrap entrypoint <>
                            "' from '" <>
                            inputModuleFile <>
                            "' to '" <>
                            outPath <>
                            ("'" :: Text)
        Build common@CommonCmdOpts {..} BuildOpts { outputFormat
                                                  , useStdlib
                                                  , stageHandlingOpt
                                                  , extraFeatures
                                                  , sandbox
                                                  } ->
            withCommonSetup common $ \modTracker mainAnns rawMainMod getMain -> do
                when useStdlib $ void $ insertDirectly modTracker stdlib
                let present =
                        map
                            (\(ns, i) ->
                                 show $ PP.pretty ns <>
                                 PP.tupled (map PP.pretty i))
                 in do logDebugN $ unlines $ "Algos:" :
                           present (rawMainMod ^. algoImports)
                       logDebugN $ unlines $ "Sfs:" :
                           present (rawMainMod ^. sfImports)
                mainMod <-
                    let ?env = ResolutionEnv
                            {modTracker = modTracker, preResolveHook = pure}
                     in registerAnd (rawMainMod ^. name) $
                        loadDepsAndResolve rawMainMod
                expr' <- getMain $ mainMod ^. decls
                let expr =
                        case expr'
                               -- FIXME this is technically not correct for edge cases
                              of
                            Lambda "_" body -> body
                            e -> e
                let sfDeps = gatherSFDeps expr
                let (mainArity, completeExpr) = mainToEnv expr
                udfs <- newIORef []
                let addUdf u = atomicModifyIORef' udfs (\l -> (u : l, ()))
                noriaPass <-
                    case outputFormat of
                        NoriaUDF -> do
                            let (streamAnn:_) =
                                    argTypes $ mainAnns ^?! _Just .
                                    ix entrypoint
                                (ftys, constr) =
                                    RS.para
                                        (\case
                                             TyAppF (_, (tys, f)) (ty, _) ->
                                                 (ty : tys, f)
                                             TyRefF r -> ([], r))
                                        streamAnn
                                Just formatter = Prelude.lookup "rust" langs
                                fields =
                                    IM.fromList $
                                    zip [0 ..] (map formatter $ reverse ftys)
                            pure $ NoriaUDFGen.generateOperators fields addUdf
                        _ -> pure pure
                gr <-
                    compile
                        (def & stageHandling .~ stageHandlingOpt &
                         transformRecursiveFunctions .~
                         ("tail-recursion" `elem` extraFeatures))
                        (def
                             { passAfterDFLowering = cleanUnits
                             , passAfterNormalize = noriaPass
                             })
                        completeExpr
                gen <-
                    case outputFormat of
                        JsonGraph -> pure JSONGen.generate
                        SimpleJavaClass -> pure JavaGen.generate
                        NoriaUDF -> do
                            udfs' <- readIORef udfs
                            NoriaUDFGen.extraOperatorProcessing sandbox udfs'
                            pure $ NoriaUDFGen.generate udfs'
                (nameSuggest, code) <-
                    flip runReaderT CodeGenOpts $
                    gen
                        CodeGenData
                            { graph = gr
                            , entryPointArity = mainArity
                            , sfDependencies = sfDeps
                            , annotations = mainAnns
                            , entryPointName = entrypoint
                            , entryPointNamespace = rawMainMod ^. name
                            }
                let outputPath0 = fromMaybe nameSuggest outputPath
                liftIO $
                    createDirectoryIfMissing
                        True
                        (FP.takeDirectory $ toString outputPath0)
                liftIO $ L.writeFile (toString outputPath0) code
                logInfoN $ "Compiled '" <> unwrap entrypoint <> "' from '" <>
                    inputModuleFile <>
                    "' to " <>
                    showCodeGen outputFormat
                logInfoN $ "Code written to '" <> outputPath0 <> "'"
  where
    withCommonSetup ::
           (m ~ ExceptT Text (LoggingT IO))
        => CommonCmdOpts
        -> (IORef ModMap -> Maybe TyAnnMap -> RawNamespace -> (forall map. ( Ixed map
                                                                           , Index map ~ Binding
                                                                           ) =>
                                                                               map -> m (IxValue map)) -> m a)
        -> IO a
    withCommonSetup CommonCmdOpts {..} f =
        runCompM logLevel $ do
            modTracker <- newIORef mempty
            (mainAnns, rawMainMod) <- readAndParse inputModuleFile
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
            f modTracker mainAnns rawMainMod getMain
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
                 (Just $ softStr "Format to emit the generated code in." <//>
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
             (O.strOption $ long "stop-on" <>
              help "Stop execution after this stage." <>
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
                   help "Enable extra (experimental) features"))) <*>
        O.switch
            (long "sandbox" <>
             help
                 "Write database linking files to a temporary directory (only used for noria codegen)")
    softStr = fillSep . map text . Str.words
    optsParser =
        hsubparser
            (command
                 "build"
                 (info
                      (Build <$> commonOptsParser <*> buildOpts)
                      (progDescDoc $ Just $ "Build the ohua graph. " <$$> "" <$$>
                       softStr
                           "The options --dump-stage and --stop-on pertain to stages. See https://ohua.rtfd.io/en/latest/debugging.html#stages." <$$>
                       fillSep
                           ("I know about the following stages:" :
                            punctuate comma (map (text . toString) knownStages)))) <>
             command
                 "dump-main-type"
                 (info
                      (flip DumpType <$> dumpOpts <*> commonOptsParser)
                      (progDesc "Dump the type of the main function")) <>
             command
                 "version"
                 (info
                      (pure ShowVersion)
                      (progDesc
                           "Show information, such as the version, about this binary.")))
    commonOptsParser =
        CommonCmdOpts <$>
        argument str (metavar "SOURCE" <> help "Source file to compile") <*>
        argument
            (eitherReader $ mapLeft toString . make . toText)
            (metavar "MAIN" <> help "Algorithm that serves as entry point" <>
             O.value "main") <*>
        optional
            (strOption $ long "output" <> metavar "PATH" <> short 'o' <>
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
