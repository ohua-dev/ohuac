module Ohua.CodeGen.NoriaUDF
    ( generateOperators
    , generate
    , suggestName
    , rewriteQueryExpressions
    , mainArgsToTableRefs
    , rewriteFieldAccess
    , preResolveHook
    ) where

import Ohua.Prelude

import qualified Data.Binary as B
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.IntMap as IM
import qualified Data.List as List
import Data.Maybe (fromJust)
import qualified Data.Text as Text
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.Encoding as LT
import qualified Data.Text.Lazy.IO as LT
import Data.Text.Prettyprint.Doc ((<+>), pretty)
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Ohua.ALang.Refs as Refs
import Ohua.CodeGen.Iface
import qualified Ohua.CodeGen.NoriaUDF.Mir as Mir
import qualified Ohua.CodeGen.NoriaUDF.Paths as Path
import Ohua.CodeGen.NoriaUDF.Types
import qualified Ohua.DFGraph as DFGraph
import qualified Ohua.Helpers.Graph as GR
import qualified Ohua.Helpers.Template as TemplateHelper
import Ohua.Helpers.Template (Substitutions)
import Ohua.Prelude hiding (First, Identity)
import Prelude ((!!))
import qualified Prelude
import qualified System.Directory as FS
import qualified System.FilePath as FS
import System.IO.Unsafe (unsafePerformIO)
import Text.Printf (printf)
import qualified System.FilePath as FP
import qualified System.IO.Temp as Temp
import qualified Data.Foldable
import qualified Data.Vector as V

import Ohua.CodeGen.NoriaUDF.Operator
import Ohua.CodeGen.NoriaUDF.LowerToMir

import Paths_ohuac

data Query = Query
    { queryOps :: [OperatorDescription]
    , queryGraph :: SerializableGraph
    } deriving (Eq, Generic)

instance B.Binary SerializableGraph
instance B.Binary Query

data InstalledQueries = InstalledQueries
    { queries :: HashMap Binding Query }
    deriving (Eq, Generic)

instance B.Binary InstalledQueries

instance Default InstalledQueries where
    def = InstalledQueries HashMap.empty

loadNoriaTemplate :: MonadIO m => FilePath -> m [TemplateHelper.Rep]
loadNoriaTemplate t =
    liftIO $ do
        path <- getDataFileName $ "templates/noria" FP.</> t
        TemplateHelper.parseTemplate <$> readFile path

doTheGenerating ::
       (MonadIO m, MonadLogger m, Foldable f)
    => f GenerationType
    -> m ()
doTheGenerating toGen = do
    templates <-
        traverse loadNoriaTemplate $
        HashMap.fromList
            [ (t, t)
            | TemplateSubstitution t _ _ <- Data.Foldable.toList toGen
            ]
    let getTemplate t =
            fromMaybe
                (error $ "Invariant broken, template not found " <> toText t) $
            HashMap.lookup t templates
    Data.Foldable.for_ toGen $ \case
        TemplateSubstitution t path subs -> do
            p <- liftIO $ FS.makeAbsolute path
            logDebugN $ "Outputting to path " <> fromString p
            outputFile path =<<
                TemplateHelper.sub
                    TemplateHelper.Opts {preserveSpace = True}
                    (getTemplate t)
                    subs
        GenerateFile path content ->
            liftIO $ writeFile path content

outputFile :: MonadIO m => FilePath -> Text -> m ()
outputFile path content =
    liftIO $ do
        FS.createDirectoryIfMissing True (FP.takeDirectory path)
        writeFile path content

patchFile ::
       (MonadIO m, MonadLogger m)
    => Maybe FilePath
    -> FilePath
    -> Substitutions
    -> m ()
patchFile mOutDir file subs = do
    tmpl <- TemplateHelper.parseTemplate <$> readFile file
    writeF file =<<
        TemplateHelper.sub TemplateHelper.Opts {preserveSpace = True} tmpl subs
  where
    writeF =
        flip (maybe writeFile) mOutDir $ \dir filename content ->
            liftIO $ outputFile (dir FP.</> filename) content

-- TODO create the state impls in map-reduce/state.rs needs sub key "state-trait-coerce-impls"
patchFiles ::
       (MonadIO m, MonadLogger m) => Maybe FilePath -> [UDFDescription] -> m ()
patchFiles mOutDir udfs =
    mapM_ (uncurry $ patchFile mOutDir) (HashMap.toList fileMap)
  where
    toMap =
        ([ Path.dataflowSourceDir <> "/ops/ohua/mod.rs" ~>
           ["link-generated-modules" ~> ["pub mod generated;"]]
         ] <>) .
        HashMap.fromListWith (HashMap.unionWith (<>))
    fileMap = toMap $ udfs >>= mkPatchesFor

extraOperatorProcessing ::
       (MonadError Error m, MonadIO m, MonadLogger m)
    => InstalledQueries
    -> [OperatorDescription]
    -> m ()
extraOperatorProcessing qs ops = do
    let udfs =
            mapMaybe
                (\case
                     Op_UDF desc -> Just desc
                     _ -> Nothing)
                ops
    doTheGenerating (udfs >>= generations)
    let allUdfs = List.nub
                  [desc
                  | (_, q) <- HashMap.toList $ queries qs
                  , Op_UDF desc <- queryOps q
                  ]
    outputFile Path.generatedOpsModFile $ Text.unlines $
        map (\u -> "pub mod " <> unwrap (udfName u ^. name) <> ";") allUdfs
    outputFile Path.generatedStatesModFile $ Text.unlines $
        mapMaybe
            (\case
                 u@(UDFDescription {udfState = Just _}) ->
                     Just $ "pub mod " <> unwrap (udfName u ^. name) <> ";"
                 _ -> Nothing)
            allUdfs
    patchFiles Nothing allUdfs

loadInstalledQueries :: MonadIO m => m InstalledQueries
loadInstalledQueries = liftIO $ do
    ext <- FS.doesFileExist qObjFile
    if ext then B.decodeFile qObjFile else return def

qObjFile = "installed.ohua-query-object"

saveInstalledQueries :: MonadIO m => InstalledQueries -> m ()
saveInstalledQueries = liftIO . B.encodeFile qObjFile

addInstalledQuery :: Binding -> Query -> InstalledQueries -> InstalledQueries
addInstalledQuery b q qs = qs { queries = HashMap.insert b q $ queries qs }

generate :: [OperatorDescription] -> CodeGen
generate compiledNodes d@CodeGenData {..} = do
    prev <- loadInstalledQueries
    serializableGraph <-
        makeGraph compiledNodes d
    tpl <- loadNoriaTemplate "udf_graph.rs"
    let subs = ["graph" ~> graphToSubs serializableGraph]
    tpl' <-
        TemplateHelper.sub TemplateHelper.Opts {preserveSpace = True} tpl subs
    let all = addInstalledQuery (entryPoint ^. name) (Query compiledNodes serializableGraph) prev
    saveInstalledQueries all
    extraOperatorProcessing all compiledNodes
    patchFile
        Nothing
        Path.udfsModFile
        [ "graph-mods" ~> ["mod " <> unwrap ep <> "_graph;" | ep <- HashMap.keys $ queries all ]
        , "graph-dispatch" ~>
          [ "\"" <>
            ep <>
            "\" => Some(Box::new(" <> ep <> "_graph::mk_graph)),"
          | (unwrap -> ep) <- HashMap.keys $ queries all
          ]
        ]
    pure $ LT.encodeUtf8 $ LT.fromStrict tpl'
  where
    entryPointName = unwrap $ entryPoint ^. name



suggestName :: NameSuggester
suggestName entryPoint =
    Path.udfsDir <> "/" <> unwrap (entryPoint ^. name) <> "_graph.rs"
