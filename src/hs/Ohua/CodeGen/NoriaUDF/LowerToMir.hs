{-# LANGUAGE MultiWayIf, ConstraintKinds #-}

module Ohua.CodeGen.NoriaUDF.LowerToMir
    ( generate
    , suggestName
    ) where

import Ohua.Prelude hiding (First, Identity)

import qualified Data.HashSet as HashSet
import Control.Lens (Simple, (%=), (^?!), ix, to, use)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.IntMap as IM
import Data.Maybe (fromJust)
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.Encoding as LT
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Text.Prettyprint.Doc ((<+>), pretty)
import Prelude ((!!))

import Ohua.CodeGen.Iface
import qualified Ohua.CodeGen.NoriaUDF.Mir as Mir
import Ohua.CodeGen.NoriaUDF.Operator
    ( ExecSemantic
    , OperatorDescription(..)
    , pattern ReductionSem
    , pattern SimpleSem
    , ToRust(..)
    , UDFDescription(UDFDescription, execSemantic, udfName)
    , (~>)
    , loadNoriaTemplate
    , patchFile
    , renderDoc
    )
import Ohua.CodeGen.NoriaUDF.Types
import qualified Ohua.DFGraph as DFGraph
import qualified Ohua.Helpers.Graph as GR
import qualified Ohua.Helpers.Template as TemplateHelper

-- data Column = InternalColumn (Int, Int) | NamedColumn Mir.Column
--     deriving (Show, Eq, Ord, Generic)
type GetGraph g a b s m
     = (MonadState s m, Field1 s s (g a b) (g a b), GR.DynGraph g)

type ScopeMap = IntMap [Scope]

type NoriaGraph opLabel edgeLabel = GR.Gr opLabel edgeLabel

type MirGraph = NoriaGraph Operator [Column]

type GeneratedMirNodes = HashMap QualifiedBinding Operator

type LitMap = IntMap [(Int, Lit)]

type AdjList a = [(a, [Mir.Column], [Word])]

type MirIndex = Word

data SerializableGraph =
    SerializableGraph
        { adjacencyList :: AdjList Mir.Node
        , sink :: (Word, [Mir.Column])
        , sources :: [(Text, Word, Int, [Mir.Column])]
        }

type OpMap = IntMap OpMapEntry

type OpMapEntry = (Mir.Node, [Mir.Column], [Mir.Column])

type Rewrite a = (a -> a)

type Field1' a b = Simple Field1 a b

type Field2' a b = Simple Field2 a b

type Field3' a b = Simple Field3 a b

type Field4' a b = Simple Field4 a b

expectNumLit :: HasCallStack => Lit -> Integer
expectNumLit (NumericLit n) = n
expectNumLit other = error $ "Expected numeric literal, found " <> show other

getLit :: IntMap [a] -> Int -> [a]
getLit m k = fromMaybe [] $ IM.lookup k m

isJoin :: Operator -> Bool
isJoin Join {} = True
isJoin _ = False

isSink :: Operator -> Bool
isSink Sink = True
isSink _ = False

isSource :: Operator -> Bool
isSource Source {} = True
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
       MonadLogger m
    => GeneratedMirNodes
    -> HashMap Binding Word
    -> DFGraph.OutGraph
    -> m (ScopeMap, MirGraph)
annotateAndRewriteQuery gMirNodes tableIndexMap graph = do
    debugLogGR "Initial Graph" iGr
    let s0 = (iGr, succ $ snd $ GR.nodeRange iGr)
    s1@(gr1, _) <- flip execStateT s0 $ collapseNth envInputs
    let g = mkScopeMap envInputs gr1
    logInfoN $ "Scope Map\n" <> show g
    debugLogGR "Graph with nth collapsed" gr1
    (gr2, i2) <- execStateT removeSuperfluousOperators s1
    (gr3, _, g2) <-
        flip execStateT (collapseMultiArcs gr2, i2, g) $ multiArcToJoin g
    pure (g2, gr3)
    -- TODO Actually, its better to put the indices as edge labels. Means I have
    -- to group when inserting the joins, but I don't have to keep adjusting the
    -- operator Id's for the Target's
  where
    iGr :: GR.Gr Operator (Int, Int)
    iGr =
        GR.mkGraph
            ((sinkId, Sink) :
             map
                 (\DFGraph.Operator {..} ->
                      ( unwrap operatorId
                      , retype2 gMirNodes tableIndexMap operatorType))
                 operators) $
        ( unwrap $ DFGraph.operator $ DFGraph.returnArc graph
        , sinkId
        , (DFGraph.index $ DFGraph.returnArc graph, 0)) :
        [ ( unwrap $ DFGraph.operator s
          , unwrap $ DFGraph.operator t
          , (DFGraph.index s, DFGraph.index t))
        | DFGraph.Arc t (DFGraph.LocalSource s) <- arcs
        ]
    sinkId = -1
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

collapseNth :: GetGraph g Operator Column s m => LitMap -> m ()
collapseNth envInputs =
    forNodes_
        (\case
             CustomOp "ohua.lang/nth" -> Just ()
             _ -> Nothing) $ \node _ ->
        sGetContext node >>= \case
            ([((0, 2), inOp)], _, _, outs) -> do
                let Just (0, NumericLit (fromIntegral -> idx)) =
                        find ((== 0) . view _1) $ envInputs `getLit` node
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

mkScopeMap :: LitMap -> NoriaGraph Operator Column -> ScopeMap
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
                          CustomOp "ohua.sql.query/group_by" -> (GroupBy cols :)
                              where cols =
                                        map
                                            (DFGraph.Target (unsafeMake preNum) .
                                             fromIntegral .
                                             expectNumLit)
                                            colNums
                                    [(_, preNum)] = pre
                                    colNums =
                                        case IM.lookup n lm of
                                            Just [(_, col)] -> [col]
                                            cols ->
                                                error $
                                                "Expected single env argument to `group_by`, found " <>
                                                maybe "none" show cols
                          -- "ohua.lang/smap" -> (SmapC :)
                          CustomOp "ohua.lang/collect" -> \(_:xs) -> xs
                          _ -> id
            ]

retype ::
       GeneratedMirNodes
    -> HashMap Binding Word
    -> NoriaGraph QualifiedBinding b
    -> NoriaGraph Operator b
retype m = GR.nmap . retype2 m

retype2 ::
       GeneratedMirNodes -> HashMap Binding Word -> QualifiedBinding -> Operator
retype2 m tm other@(QualifiedBinding namespace name) =
    case namespace of
        ["ohua", "sql", "rel"] -> Source (tm HashMap.! name) $ unwrap name
        ["intrinsic"] ->
            case name of
                "sink" -> error "No longer exists"
                "source" -> error "sources now need table names"
                _ -> error $ "Unknown intrinsic " <> showT name
        ["ohua", "lang"]
            | name == "(,)" -> Identity -- Needs to become a project instead
        _ -> fromMaybe (CustomOp other) $ HashMap.lookup other m

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
        let adjustment
                | null p1Cols = error "p1cols should not be empty"
                | otherwise = succ $ maximum (map fst p1Cols)
        _1 %= GR.insEdges [(p1, id, p1Cols), (p2, id, p2Cols)]
        pure (p1Cols ++ map (first (adjustment +)) p2Cols, id)
    -- UDF {
    --     function_name: String,
    --     //Do I need this?
    --     input: Vec<Column>,
    --     group_by: Vec<Column>,
    -- },

-- pub enum Operator {
--     Not,
--     And,
--     Or,
--     Like,
--     NotLike,
--     Equal,
--     NotEqual,
--     Greater,
--     GreaterOrEqual,
--     Less,
--     LessOrEqual,
--     In,
--     Is,
-- }
instance ToRust SerializableGraph where
    asRust graph =
        "UDFGraph" <>
        recordSyn
            [ "adjacency_list" ~> "vec!" <>
              PP.list (map toAListElem $ adjacencyList graph)
            , "sink" ~>
              let (n, idxs) = sink graph
               in PP.tupled [pretty n, "vec!" <> PP.list (encodeCols idxs)]
            , "sources" ~> "vec!" <>
              PP.list
                  (map (\(t, i, i2, s) ->
                            PP.tupled
                                [ pretty t
                                , pretty i
                                , pretty i2
                                , "vec!" <> PP.list (encodeCols s)
                                ]) $
                   sources graph)
            ]
      where
        toAListElem (node, cols, preds) =
            PP.tupled
                [ mirNodeToRust node
                , "vec!" <> PP.list (encodeCols cols)
                , "vec!" <> PP.list (map pretty preds)
                ]
        encodeOpt f =
            maybe "Option::None" (\s -> "Option::Some" <> PP.parens (f s))
        encodeCond (Mir.Comparison op v) =
            "FilterCondition::Comparison" <>
            PP.parens (encodeOperator op <> "," <> encodeValue v)
        encodeOperator = ("Operator::" <>) . PP.pretty . showT
        encodeValue =
            \case
                Mir.ConstantValue v ->
                    "Value::Constant" <> PP.parens (encodeValueConstant v)
                Mir.ColumnValue c -> "Value::Column" <> PP.parens (encodeCol c)
        encodeValueConstant =
            ("DataType::" <>) . \case
                NumericLit n -> "Int" <> PP.parens (pretty n)
        mirNodeToRust =
            ("MirNodeType::" <>) . \case
                Mir.Identity _ -> "Identity"
                Mir.Filter {..} ->
                    "Filter" <+>
                    recordSyn
                        [ "conditions" ~>
                          ppVec (map (encodeOpt encodeCond) conditions)
                        ]
                Mir.Regular {..} ->
                    "UDFBasic" <+>
                    recordSyn
                        [ ( "function_name"
                          , PP.dquotes (pretty nodeFunction) <> ".to_string()")
                        , ("indices", ppVec (encodeCols indices))
                        , ( "execution_type"
                          , "ExecutionType::" <>
                            case executionType of
                                Mir.Reduction {..} ->
                                    "Reduction" <>
                                    recordSyn
                                        [ ( "group_by"
                                          , "vec!" <>
                                            PP.list (encodeCols groupBy))
                                        ]
                                Mir.Simple i ->
                                    "Simple" <> recordSyn [("carry", pretty i)])
                        ]
                Mir.Join {..} ->
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
        encodeCol Mir.Column {..} =
            "Column::new" <>
            PP.tupled [encodeOpt pretty table, PP.dquotes $ pretty name]
        encodeCols = map encodeCol

completeOutputColsFor :: OpMapEntry -> [Mir.Column]
completeOutputColsFor i = i ^. _2 <> i ^. _3

toMirCol :: DFGraph.Target -> Mir.Column
toMirCol DFGraph.Target {..} =
    Mir.Column
        { table = Nothing
        , name = showT $ "o" <> (pretty operator) <> "_i" <> (pretty index)
        }

toSerializableGraph2 ::
       [UDFDescription] -> ScopeMap -> MirGraph -> SerializableGraph
toSerializableGraph2 udfs cm mg =
    SerializableGraph
        { adjacencyList =
              [ (entry ^. _1, completeOutputColsFor entry, map toNIdx ins)
              | n <- nonSinkSourceNodes
              , let entry = opMap IM.! n
                    ins = GR.pre mg n
              ]
        , sink =
              let [(s, _, l)] = GR.inn mg $ fst sink
               in (toNIdx s, completeOutputColsFor $ opMap ^?! ix s)
        , sources = sources
        }
  where
    columnDemand =
        IM.fromList
            [ ( id
              , case op of
                    Join {} -> undefined
                    other -> selfDemand <> scopeDemand <> downstreamDemand)
            | (_, id) <- indexMapping
            , let (ins, _, op, outs) = GR.context mg id
                  downstreamDemand =
                      HashSet.unions $ map ((columnDemand IM.!) . snd) outs
                  scopeDemand =
                      HashSet.fromList
                          [ Left (unwrap fid, i)
                          | GroupBy b <- cm IM.! id
                          , DFGraph.Target fid i <- b
                          ]
                  selfDemand =
                      HashSet.fromList $
                      case op of
                          Join {} -> error "impossible"
                          Filter f -> HashMap.keys f
                          Projection p -> map Left p
                          Identity -> fromIn
                          Sink -> fromIn
                          Source {} -> []
                          CustomOp _ -> fromIn
                  fromIn =
                      [ Left c
                      | (cols, _) <- ins
                      , c@(_, idx) <- cols
                      , idx /= negate 1
                      ]
            ]
    opMap =
        IM.fromList
            [ (oldId, (undefined, cols))
            | (newId, oldId) <- indexMapping
            , let (ins, _, op, outs) = GR.context mg n
                  cols =
                      case op of
                          _ -> stdCols
                  [((opMap IM.!) -> parent)] = ins
                  stdCols = parent ^. _2
            ]
    indexMapping :: [(Word, Int)]
    indexMapping =
        zip
            [0 ..] -- new indices corresponding to index in this list
            (fst sink : -- sink node will be inserted first from noria
             map (^. _3) (sortOn (^. _2) sources) -- then follow all base tables
              ++
             nonSinkSourceNodes)
    nonSinkSourceNodes :: [Int]
    nonSinkSourceNodes =
        [ n
        | (n, op) <- GR.labNodes mg
        , case op -- and on this end we must filter all those nodes
                          -- we've already explicitly inserted before
                of
              Sink -> False
              Source {} -> False
              _ -> True
        ]
    sources =
        [ ( name
          , idx
          , s
          , map (Mir.Column (Just name) . showT) [0 .. maximum (map fst labels)])
        | (s, Source idx name) <- GR.labNodes mg
        , let labels = concatMap (^. _3) $ GR.out mg s
        ]

toSerializableGraph ::
       [UDFDescription] -> ScopeMap -> MirGraph -> SerializableGraph
toSerializableGraph udfs cm mg =
    SerializableGraph
        { adjacencyList =
              [ (entry ^. _1, completeOutputColsFor entry, map toNIdx ins)
              | (_, n) <- drop 2 indexMapping
              , let entry = opMap IM.! n
                    ins = GR.pre mg n
              ]
        , sink =
              let [(s, _, l)] = GR.inn mg $ fst sink
               in (toNIdx s, completeOutputColsFor $ opMap ^?! ix s)
        , sources = sources
        }
  where
    execSemMap :: QualifiedBinding -> Maybe ExecSemantic
    execSemMap =
        flip HashMap.lookup $ HashMap.fromList $
        map (\UDFDescription {..} -> (udfName, execSemantic)) udfs
    opMap :: OpMap
    opMap =
        IM.fromList
            [ (n, (newOp, flattenCtx ctx, cols))
            | n <- nonSinkSourceNodes
            , let (ins, _, op, outs) = GR.context mg n
                  ctx = cm IM.! n
                  indices =
                      case ins of
                          [] -> []
                          [(edges, n)] ->
                              map (colFrom n . fst) $ sortOn snd edges
                          _ -> error $ "Too many ancestors for " <> show op
                  cols = case op of
                      Join {} -> cols1 <> flattenCtx ctx <> cols2 -- dirty hack
                      _ | null outs -> []
                        | otherwise -> normalCols
                    where
                      normalCols =
                          map
                              (colFrom n)
                              [0 .. maximum
                                        [ outIdx
                                        | out <- outs
                                        , (outIdx, _) <- fst out
                                        ]]
                      -- For dirty hack
                      [(e1, _), (e2, _)] = ins
                      (cols1, cols2) = splitAt (length e1) normalCols
                  newOp =
                      case op of
                          CustomOp o ->
                              Mir.Regular
                                  { nodeFunction = o
                                  , indices = indices
                                  , executionType =
                                        case execSem of
                                            ReductionSem ->
                                                Mir.Reduction $ flattenCtx ctx
                                            SimpleSem ->
                                                Mir.Simple $ fromIntegral $
                                                length (flattenCtx ctx)
                                  }
                              where Just execSem = execSemMap o
                          Join _ ->
                              Mir.Join
                                  { mirJoinProject =
                                        flattenCtx ctx <> adjToProduced p1 <>
                                        adjToProduced p2
                                  , left = flattenCtx ctx
                                  , right = flattenCtx ctx
                                  }
                              where [p1, p2] = ins
                          Projection _ -> unimplemented
                          Identity -> Mir.Identity $ opMap ^?! ix p . _3
                              where [(_, p)] = ins
                          Sink -> error "impossible"
                          Source {} -> error "impossible"
                          Filter f ->
                              let elems = HashMap.toList f
                               in Mir.Filter
                                      { indices =
                                            map
                                                (either (uncurry colFrom) id .
                                                 fst)
                                                elems
                                      , conditions = map (Just . snd) elems
                                      }
            ]
    adjToProduced (edges, opid) = map (\(out, _) -> colFrom opid out) edges
    colFrom op = toMirCol . DFGraph.Target (unsafeMake op)
    [sink] = filter (isSink . snd) (GR.labNodes mg)
    sources =
        [ ( name
          , idx
          , s
          , map (Mir.Column (Just name) . showT) [0 .. maximum (map fst labels)])
        | (s, Source idx name) <- GR.labNodes mg
        , let labels = concatMap (^. _3) $ GR.out mg s
        ]
    indexMapping :: [(Word, Int)]
    indexMapping =
        zip
            [0 ..] -- new indices corresponding to index in this list
            (fst sink : -- sink node will be inserted first from noria
             map (^. _3) (sortOn (^. _2) sources) -- then follow all base tables
              ++ nonSinkSourceNodes)
    nonSinkSourceNodes :: [Int]
    nonSinkSourceNodes =
             [ n
             | (n, op) <- GR.labNodes mg
             , case op of -- and on this end we must filter all those nodes
                          -- we've already explicitly inserted before
                   Sink -> False
                   Source {} -> False
                   _ -> True
             ]
    toNIdx :: Int -> Word
    toNIdx = ((IM.fromList $ map swap indexMapping) IM.!)
    scopeSize = fromIntegral . length . flattenCtx

flattenCtx :: [Scope] -> [Mir.Column]
flattenCtx = (>>= \(GroupBy l) -> map toMirCol l)

unimplemented :: HasCallStack => a
unimplemented = error "Function or branch not yet implemented"

noriaMirSourceDir :: IsString s => s
noriaMirSourceDir = "noria-server/mir/src"

suggestName :: NameSuggester
suggestName entryPoint =
    noriaMirSourceDir <> "/udfs/" <> unwrap (entryPoint ^. name) <> "_graph.rs"

generate :: HashMap Binding Word -> [OperatorDescription] -> CodeGen
generate tableIndexMap compiledNodes CodeGenData {..} = do
    let (mirNodes, udfs) =
            partitionEithers $
            map
                (\case
                     Op_MIR m -> Left m
                     Op_UDF u -> Right u)
                compiledNodes
    (ctxMap, iGr) <-
        annotateAndRewriteQuery (HashMap.fromList mirNodes) tableIndexMap graph
    debugLogGR "Annotated graph:" iGr
    tpl <- loadNoriaTemplate "udf_graph.rs"
    let subs =
            [ "graph" ~>
              [renderDoc $ asRust $ toSerializableGraph udfs ctxMap iGr]
            ]
    tpl' <-
        TemplateHelper.sub TemplateHelper.Opts {preserveSpace = True} tpl subs
    patchFile
        Nothing
        (noriaMirSourceDir <> "/udfs/mod.rs")
        [ "graph-mods" ~> ["mod " <> entryPointName <> "_graph;"]
        , "graph-dispatch" ~>
          [ "\"" <> entryPointName <> "\" => Some(" <> entryPointName <>
            "_graph::mk_graph()),"
          ]
        ]
    pure $ LT.encodeUtf8 $ LT.fromStrict tpl'
  where
    entryPointName = unwrap $ entryPoint ^. name
