{-# LANGUAGE TypeApplications, MultiWayIf, ConstraintKinds #-}
module Ohua.CodeGen.NoriaUDF.Mir
    ( generate
    ) where

import Ohua.Prelude hiding (First, Identity)

import Control.Arrow ((***))
import Control.Category ((>>>))
import Control.Comonad (extract)
import Control.Lens (Simple, (%=), (<>=), (^..), (^?!), ix, to, use)
import Control.Monad.RWS (runRWST)
import Control.Monad.Writer (runWriterT, tell)
import qualified Data.Foldable
import qualified Data.Functor.Foldable as RS
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.Maybe (fromJust)
import qualified Data.Text as T
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.Encoding as LT
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Text.Prettyprint.Doc ((<+>), pretty)
import qualified Data.Text.Prettyprint.Doc.Render.Text as PP
import Data.Traversable (for)
import Ohua.Standalone (PreResolveHook)
import Prelude ((!!))
import System.Directory (createDirectoryIfMissing)
import qualified System.FilePath as FP
import qualified System.IO.Temp as Temp

import Ohua.ALang.Lang
import Ohua.ALang.PPrint (ohuaDefaultLayoutOpts, quickRender)
import qualified Ohua.ALang.Passes as ALang (normalize)
import qualified Ohua.ALang.Refs as ALang
import Ohua.ALang.Util (findFreeVariables)
import Ohua.CodeGen.Iface
import qualified Ohua.CodeGen.JSONObject as JSONObject
import qualified Ohua.DFGraph as DFGraph
import qualified Ohua.Frontend.NS as NS
import qualified Ohua.Helpers.Graph as GR
import Ohua.Helpers.Template (Substitutions, Template)
import qualified Ohua.Helpers.Template as TemplateHelper
import Ohua.CodeGen.NoriaUDF.Operator (ToRust(..), FData, (~>), loadNoriaTemplate, renderDoc, patchFile)

type Column = (Int, Int)

data Scope =
    GroupBy [DFGraph.Target]
    -- | SmapC   -- Add this eventually
    deriving (Show)

data Operator
    = CustomOp QualifiedBinding
    | Join { joinOn :: [Scope] }
    | Projection [Column]
    | Identity
    | Sink
    | Source
    deriving (Show)

type GetGraph g a b s m
     = (MonadState s m, Field1 s s (g a b) (g a b), GR.DynGraph g)

type ScopeMap = IntMap [Scope]

type NoriaGraph opLabel edgeLabel = GR.Gr opLabel edgeLabel

type MirGraph = NoriaGraph Operator [Column]

type LitMap = IntMap [(Int, Lit)]

type AdjList a = [(a, [MirColumn], [Word])]

-- | (isFromMain, Index)
type MirColumn = DFGraph.Target

type MirIndex = Word

data ExecutionType = Reduction
    { groupBy :: [MirColumn]
    }

data MirNode
    = Regular { nodeFunction :: QualifiedBinding
              , indices :: [MirColumn]
              , executionType :: ExecutionType }
    | MirJoin { mirJoinProject :: [MirColumn]
              , left :: [MirColumn]
              , right :: [MirColumn] }
    | MirIdentity [MirColumn]
    -- | MirJoin
    -- | MirProjection

data SerializableGraph = SerializableGraph
    { adjacencyList :: AdjList MirNode
    , sink :: (Word, [MirColumn])
    , source :: [MirColumn]
    }

type OpMap = IntMap OpMapEntry

type OpMapEntry = (MirNode, [MirColumn], [MirColumn])

type Rewrite a = (a -> a)

type Field1' a b = Simple Field1 a b

type Field2' a b = Simple Field2 a b

type Field3' a b = Simple Field3 a b

type Field4' a b = Simple Field4 a b

isJoin :: Operator -> Bool
isJoin Join {} = True
isJoin _ = False

isSink :: Operator -> Bool
isSink Sink = True
isSink _ = False

isSource :: Operator -> Bool
isSource Source = True
isSource _ = False

groupOnInt :: [(a, Int)] -> [([a], Int)]
groupOnInt =
    fmap swap . IM.toList . IM.fromListWith (++) . fmap (second pure) .
    fmap swap

debugLogGR :: (Show a, Show b, MonadLogger m) => Text -> GR.Gr a b -> m ()
debugLogGR msg gr = logDebugN (msg <> "\n" <> toText (GR.prettify gr))

forNodes_ ::
       GetGraph g a b s m => (a -> Maybe c) -> (GR.Node -> c -> m x) -> m ()
forNodes_ pred ac = do
    nodes <- use $ _1 . to GR.labNodes
    for_ nodes $ \(n, lab) -> maybe (pure ()) (void . ac n) $ pred lab

mkLitMap :: [DFGraph.DirectArc Lit] -> LitMap
mkLitMap arcs =
    IM.fromListWith
        (++)
        [ (unwrap $ DFGraph.operator t, [(DFGraph.index t, l)])
        | DFGraph.Arc t (DFGraph.EnvSource l') <- arcs
        , l <-
              case l' of
                  EnvRefLit {} -> []
                  l'' -> [l'']
        ]

-- TODO
-- - Rewrite literals to projection
-- - Incorporate indices from previously compiled udfs
annotateAndRewriteQuery ::
       MonadLogger m => [FData] -> DFGraph.OutGraph -> m (ScopeMap, MirGraph)
annotateAndRewriteQuery compiledNodes graph = do
    debugLogGR "Initial Graph" iGr
    let s0 = (iGr, succ $ snd $ GR.nodeRange iGr)
    s1@(gr1, _) <- flip execStateT s0 $ collapseNth envInputs
    let g = mkScopeMap envInputs gr1
    logInfoN $ "Scope Map\n" <> show g
    debugLogGR "Graph with nth collapsed" gr1
    (gr2, i2) <- execStateT removeSuperfluousOperators (first retype s1)
    (gr3, _, g2) <-
        flip execStateT (collapseMultiArcs gr2, i2, g) $ multiArcToJoin g
    pure (g2, gr3)
    -- TODO Actually, its better to put the indices as edge labels. Means I have
    -- to group when inserting the joins, but I don't have to keep adjusting the
    -- operator Id's for the Target's
  where
    iGr :: GR.Gr QualifiedBinding (Int, Int)
    iGr =
        GR.mkGraph
            (map (first unwrap) $ (sourceId, "intrinsic/source") :
             (sinkId, "intrinsic/sink") :
             map
                 (\DFGraph.Operator {..} -> (operatorId, operatorType))
                 operators) $
        ( unwrap $ DFGraph.operator $ DFGraph.returnArc graph
        , unwrap sinkId
        , (DFGraph.index $ DFGraph.returnArc graph, 0)) :
        [ ( unwrap $ DFGraph.operator s
          , unwrap $ DFGraph.operator t
          , (DFGraph.index s, DFGraph.index t))
        | DFGraph.Arc t (DFGraph.LocalSource s) <- arcs
        ] ++
        mainArgs
    mainArgs =
        [ (unwrap sourceId, unwrap operator, (unwrap i, index))
        | DFGraph.Arc DFGraph.Target {..} (DFGraph.EnvSource (EnvRefLit i)) <-
              arcs
        ]
    sourceId = -1
    sinkId = -2
    sinkArc = DFGraph.Arc (DFGraph.Target sinkId 0) (DFGraph.returnArc graph)
    envInputs = mkLitMap arcs
    operators = DFGraph.operators graph
    arcs = DFGraph.direct $ DFGraph.arcs graph

getNodesOfType :: GetGraph g opLabel a s m => (opLabel -> Bool) -> m [GR.Node]
getNodesOfType f = use $ _1 . to (map fst . filter (f . snd) . GR.labNodes)

sDelNode :: GetGraph g vertexLabel edgeLabel s m => GR.Node -> m ()
sDelNode node = _1 %= (GR.delNode node)

sGetContext ::
       GetGraph g opLabel edgeLabel s m
    => GR.Node
    -> m (GR.Context opLabel edgeLabel)
sGetContext node = use $ _1 . to (flip GR.context node)

sInsEdge :: GetGraph g a b s m => GR.LEdge b -> m ()
sInsEdge edge = _1 %= GR.insEdge edge

collapseMultiArcs ::
       NoriaGraph opLabel edgeLabel -> NoriaGraph opLabel [edgeLabel]
collapseMultiArcs = GR.gmap $ (_1 %~ groupOnInt) . (_4 %~ groupOnInt)

collapseNth :: GetGraph g QualifiedBinding Column s m => LitMap -> m ()
collapseNth envInputs =
    forNodes_
        (\case
             "ohua.lang/nth" -> Just ()
             _ -> Nothing) $ \node _ ->
        sGetContext node >>= \case
            ([((0, 2), inOp)], _, _, outs) -> do
                let Just (0, NumericLit (fromIntegral -> idx)) =
                        find ((== 0) . view _1) $ envInputs IM.! node
                sDelNode node
                for_ outs $ \((0, inIdx), tOp) ->
                    sInsEdge (inOp, tOp, (idx, inIdx))
            other -> error $ "scope has incorrect shape: " <> show other

dropNodes :: GetGraph g a Column s m => (a -> Bool) -> m ()
dropNodes f =
    dropNodesProjecting
        (\n ->
             if f n
                 then Just id
                 else Nothing)

dropNodesProjecting ::
       GetGraph g a Column s m => (a -> Maybe (Int -> Int)) -> m ()
dropNodesProjecting pred =
    forNodes_ pred $ \node project -> do
        (ins, _, lab, outs) <- sGetContext node
        let inMap' =
                sortOn
                    fst
                    [ (inIdx, (outIdx, source))
                    | ((outIdx, inIdx), source) <- ins
                    ]
        assertM $
            and
                [ i == i' && outIdx == 0
                | (i, (i', (outIdx, _))) <- zip [0 ..] inMap'
                ]
        let inMap = map snd inMap'
        sDelNode node
        for_ outs $ \((outIdx, inIdx), target) ->
            let (sIdx, sOp) = inMap !! project outIdx
             in sInsEdge (sOp, target, (outIdx, inIdx))

removeSuperfluousOperators :: GetGraph g Operator Column s m => m ()
removeSuperfluousOperators =
    dropNodesProjecting $ \case
        CustomOp o ->
            case o of
                "ohua.lang/smapFun" -> Just $ const 0
                "ohua.lang/collect" -> Just $ const 1
                "ohua.sql.query/group_by" -> Just toFirstInput
                _ -> Nothing
        _ -> Nothing
  where
    toFirstInput _ = 0

mkScopeMap :: LitMap -> NoriaGraph QualifiedBinding Column -> ScopeMap
mkScopeMap lm gr = m
  where
    m =
        IM.fromList
            [ ( n
              , ownCtx $
                case pre of
                    [] -> []
                    _ ->
                        maximumBy (compare `on` length) $ map (m IM.!) $
                        map snd pre)
            | n <- GR.nodes gr
            , let (pre, _, label, _) = GR.context gr n
                  ownCtx =
                      case label of
                          "ohua.sql.query/group_by" ->
                              let cols =
                                      map
                                          (\case
                                               NumericLit n ->
                                                   DFGraph.Target
                                                       (unsafeMake $ snd pre') $
                                                   fromIntegral n
                                                   where [pre'] = pre
                                               _ -> error "NO!") $
                                      map snd $
                                      sortOn fst $
                                      lm IM.!
                                      n
                               in (GroupBy cols :)
                          -- "ohua.lang/smap" -> (SmapC :)
                          "ohua.lang/collect" -> \(_:xs) -> xs
                          _ -> id
            ]

retype :: NoriaGraph QualifiedBinding b -> NoriaGraph Operator b
retype =
    GR.nmap $ \case
        "intrinsic/sink" -> Sink
        "intrinsic/source" -> Source
        "ohua.lang/(,)" -> Identity -- Needs to become a project instead
        other -> CustomOp other

-- TODO Update scopes
multiArcToJoin ::
       ( a ~ Operator
       , b ~ [Column]
       , GetGraph g a b s m
       , Field2' s GR.Node
       , Field3' s ScopeMap
       )
    => ScopeMap
    -> m ()
multiArcToJoin ctxMap = do
    gr <- use _1
    for_ (GR.nodes gr) $ \node -> do
        (preds, _, lab, _) <- sGetContext node
        unless (isJoin lab || null preds) $ do
            (ncols, npid) <- handle preds
            _1 %= GR.insEdge (npid, node, ncols) .
                GR.delEdges [(p, node) | (_, p) <- preds]
  where
    getCtx = pure . fromJust . flip IM.lookup ctxMap
    getLabel n = gets (\(g, _) -> fromJust $ GR.lab g n)
    mkNode lab =
        state
            (\s ->
                 let i = s ^. _2
                  in (i, s & _1 %~ GR.insNode (i, lab) & _2 %~ succ))
    handle [x] = pure x
    handle ((p1Cols, p1):ps) = do
        (p2Cols, p2) <- handle ps
        ctx1 <- getCtx p1
        ctx2 <- getCtx p2
        let (lowerCtx, upperCtx, isSame) =
                let l1 = length ctx1
                    l2 = length ctx2
                 in if | l1 == l2 -> (ctx1, ctx2, True)
                       | length ctx1 > length ctx2 -> (ctx2, ctx1, False)
                       | otherwise -> (ctx1, ctx2, False)
        id <- mkNode $ Join lowerCtx
        _3 %= IM.insert id lowerCtx
        -- TODO update scopes
        _1 %= GR.insEdges [(p1, id, p1Cols), (p2, id, p2Cols)]
        pure (p1Cols ++ p2Cols, id)
    -- UDF {
    --     function_name: String,
    --     //Do I need this?
    --     input: Vec<Column>,
    --     group_by: Vec<Column>,
    -- },

instance ToRust SerializableGraph where
    asRust graph =
        "UDFGraph" <>
        recordSyn
            [ "adjacency_list" ~> "vec!" <>
              PP.list (map toAListElem $ adjacencyList graph)
            , "sink" ~>
              let (n, idxs) = sink graph
               in PP.tupled [pretty n, "vec!" <> PP.list (encodeCols idxs)]
            , "source" ~> "vec!" <> PP.list (encodeCols $ source graph)
            ]
      where
        toAListElem (node, cols, preds) =
            PP.tupled
                [ mirNodeToRust node
                , "vec!" <> PP.list (encodeCols cols)
                , "vec!" <> PP.list (map pretty preds)
                ]
        mirNodeToRust =
            ("MirNodeType::" <>) . \case
                MirIdentity _ -> "Identity"
                Regular {..} ->
                    "UDFBasic" <+>
                    recordSyn
                        [ ( "function_name"
                          , PP.dquotes (pretty nodeFunction) <> ".to_string()")
                        , ("indices", ppVec (encodeCols indices))
                        , ( "execution_type"
                          , "ExecutionType::" <>
                            case executionType of
                                Reduction {..} ->
                                    "Reduction" <>
                                    recordSyn
                                        [ ( "group_by"
                                          , "vec!" <>
                                            PP.list (encodeCols groupBy))
                                        ])
                        ]
                MirJoin {..} ->
                    "Join" <+>
                    recordSyn
                        [ ("on_left", ppVec $ encodeCols left)
                        , ("on_right", ppVec $ encodeCols right)
                        , ("project", ppVec $ encodeCols mirJoinProject)
                        ]
        recordSyn =
            PP.encloseSep PP.lbrace PP.rbrace PP.comma .
            map (uncurry $ PP.surround ": ")
        ppVec l = "vec!" <> PP.list l
        encodeCol DFGraph.Target {..} =
            "Column::new" <>
            PP.tupled
                [ "Option::None"
                , PP.dquotes $ "o" <> pretty (unwrap operator) <> "_i" <>
                  pretty index
                ]
        encodeCols = map encodeCol

completeOutputColsFor :: OpMapEntry -> [MirColumn]
completeOutputColsFor i = i ^. _2 <> i ^. _3

toSerializableGraph :: ScopeMap -> MirGraph -> SerializableGraph
toSerializableGraph cm mg =
    SerializableGraph
        { adjacencyList =
              [ (entry ^. _1, completeOutputColsFor entry, map toNIdx ins)
              | (_, n) <- drop 2 indexMapping
              , let entry = opMap IM.! n
                    ins = GR.pre mg n
              ]
        , sink =
              let [sink] = filter (isSink . snd) (GR.labNodes mg)
                  [(s, _, l)] = GR.inn mg $ fst sink
               in (toNIdx s, completeOutputColsFor $ opMap ^?! ix s)
        , source =
              let [src] = filter (isSource . snd) (GR.labNodes mg)
                  labels = concatMap (^. _3) $ GR.out mg (fst src)
               in map (colFrom (-1)) [0 .. maximum (map fst labels)]
        }
  where
    opMap :: OpMap
    opMap =
        IM.fromList
            [ (n, (newOp, flattenCtx ctx, cols))
            | (_, n) <- drop 2 indexMapping
            , let (ins, _, op, outs) = GR.context mg n
                  ctx = cm IM.! n
                  indices =
                      case ins of
                          [] -> []
                          [(edges, n)] ->
                              map (colFrom n . fst) $ sortOn snd edges
                          _ -> error $ "Too many ancestors for " <> show op
                  cols
                      | null outs = []
                      | otherwise =
                          map
                              (colFrom n)
                              [0 .. maximum
                                        [ outIdx
                                        | out <- outs
                                        , (outIdx, _) <- fst out
                                        ]]
                  newOp =
                      case op of
                          CustomOp o ->
                              Regular
                                  { nodeFunction = o
                                  , indices = indices
                                  , executionType = Reduction $ flattenCtx ctx
                                  }
                          Join _ ->
                              MirJoin
                                  { mirJoinProject =
                                        flattenCtx ctx <> adjToProduced p1 <>
                                        adjToProduced p2
                                  , left = flattenCtx ctx
                                  , right = flattenCtx ctx
                                  }
                              where [p1, p2] = ins
                          Projection _ -> unimplemented
                          Identity -> MirIdentity $ opMap ^?! ix p . _3
                              where [(_, p)] = ins
                          Sink -> error "impossible"
                          Source -> error "impossible"
            ]
    adjToProduced (edges, opid) = map (\(out, _) -> colFrom opid out) edges
    colFrom op = DFGraph.Target (unsafeMake op)
    indexMapping :: [(Word, Int)]
    indexMapping = zip [0 ..] (-1 : -2 : filter (>= 0) (GR.nodes mg))
    toNIdx :: Int -> Word
    toNIdx = ((IM.fromList $ map swap indexMapping) IM.!)
    scopeSize = fromIntegral . length . flattenCtx

flattenCtx :: [Scope] -> [MirColumn]
flattenCtx = (>>= \(GroupBy l) -> l)

unimplemented :: HasCallStack => a
unimplemented = error "Function or branch not yet implemented"

noriaMirSourceDir :: IsString s => s
noriaMirSourceDir = "noria-server/mir/src"

generate :: [FData] -> CodeGen
generate compiledNodes CodeGenData {..} = do
    (ctxMap, iGr) <- annotateAndRewriteQuery compiledNodes graph
    debugLogGR "Annotated graph:" iGr
    tpl <- loadNoriaTemplate "udf_graph.rs"
    let subs =
            ["graph" ~> [renderDoc $ asRust $ toSerializableGraph ctxMap iGr]]
    tpl' <-
        TemplateHelper.sub TemplateHelper.Opts {preserveSpace = True} tpl subs
    patchFile
        Nothing
        (noriaMirSourceDir <> "/udfs/mod.rs")
        [ "graph-mods" ~> ["mod " <> unwrap entryPointName <> "_graph;"]
        , "graph-dispatch" ~>
          [ "\"" <> unwrap entryPointName <> "\" => Some(" <>
            unwrap entryPointName <>
            "_graph::mk_graph()),"
          ]
        ]
    pure (sugg, LT.encodeUtf8 $ LT.fromStrict tpl')
  where
    sugg = noriaMirSourceDir <> "/udfs/" <> unwrap entryPointName <> "_graph.rs"
