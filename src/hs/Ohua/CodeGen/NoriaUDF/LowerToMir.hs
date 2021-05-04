{-# LANGUAGE MultiWayIf, ConstraintKinds, TemplateHaskell #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}

module Ohua.CodeGen.NoriaUDF.LowerToMir
    ( generate
    , suggestName
    ) where

import Ohua.Prelude hiding (First, Identity)

import Control.Lens (Simple, (%=), (^?!), ix, to, use)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.IntMap as IM
import Data.Maybe (fromJust)
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.IO as LT
import qualified Data.Text.Lazy.Encoding as LT
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Text.Prettyprint.Doc ((<+>), pretty)
import Prelude ((!!))
import qualified Prelude
import Text.Printf (printf)

import qualified Ohua.ALang.Refs as Refs
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

import qualified Data.GraphViz as GraphViz
import qualified Data.GraphViz.Printing as GraphViz

-- data Column = InternalColumn (Int, Int) | NamedColumn Mir.Column
--     deriving (Show, Eq, Ord, Generic)
type GetGraph g a b s m
     = (MonadState s m, Field1 s s (g a b) (g a b), GR.DynGraph g)

type ScopeMap = IntMap [GScope SomeColumn]

type Gr = GR.Gr

type OperatorGraph = Gr Operator [Column]

type MirGraph = Gr (Mir.Node, [Mir.Column]) ()

type GeneratedMirNodes = HashMap QualifiedBinding Operator

type LitMap = IntMap [(Int, Lit)]

type AdjList a = [(a, [Mir.Column], [Word])]

data SerializableGraph =
    SerializableGraph
        { adjacencyList :: AdjList Mir.Node
        , sink :: (Word, [Mir.Column])
        , sources :: [(Word, Int, [Mir.Column])]
        }
    deriving (Show)

type OpMap = IntMap OpMapEntry

type OpMapEntry = (Mir.Node, [Mir.Column], [Mir.Column])

type Rewrite a = (a -> a)

type Field1' a b = Simple Field1 a b

type Field2' a b = Simple Field2 a b

type Field3' a b = Simple Field3 a b

type Field4' a b = Simple Field4 a b

quickDumpGrAsDot :: (GraphViz.Labellable a, GraphViz.Labellable b, GR.Graph g, MonadIO m) => FilePath -> g a b -> m ()
quickDumpGrAsDot f = liftIO . LT.writeFile f . GraphViz.renderDot . GraphViz.toDot . GraphViz.graphToDot GraphViz.quickParams


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

-- roots :: GR.Graph gr => gr a b -> [GR.Node]
-- roots gr = filter (null . GR.pre gr) $ GR.nodes gr

-- -- | Semantics notes for this function:
-- --   - When inserting ancestors the behavior is unspecified
-- --   - graph must be acyclic
-- --   - Successors are calculated before the action is called
-- forNodesTopo_ ::
--        GetGraph g a b s m => (a -> Maybe c) -> (GR.Node -> c -> m x) -> m ()
-- forNodesTopo_ pred ac = do
--     gr0 <- use _1
--     void $ iterateUntilM null
--         (\(x:xs) -> do
--              l <- use _2 . to (flip GR.lab x)
--              su <- use _2 . to (flip GR.suc x)
--              maybe (pure ()) ac (pred l)
--              pure xs) (roots gr0)

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

handleSuperfluousEdgesAndCtrl :: (GR.DynGraph g, MonadLogger m) => (a -> Bool) -> g a () -> m (g a ())
handleSuperfluousEdgesAndCtrl isCtrl =
    -- fmap (\g -> GR.labnfilter
    --          (\case (n, l) | isCtrl l -> if length (GR.pre g n) > 1 then error "Not yet implemented" else False
    --                 _ -> True ) g) .
    \g ->
    let tc = GR.tc g
        g' = remSuperfluousEdges tc g
        ctrlWithTooManyParents =
            [ n
            | (n, l) <- GR.labNodes g'
            , isCtrl l
            , length (GR.pre g' n) > 1
            ]
    in
        if null ctrlWithTooManyParents
        then pure g'
        else do
            logErrorN $ "Too many parents for ctrl nodes " <> show ctrlWithTooManyParents
            error "abort"
  where
    remSuperfluousEdges tc g = foldr' GR.delLEdge g
        [ (p, n, ())
        | n <- GR.nodes g
        , let pre = GR.pre g n
        , (p:other) <- tails pre
        , o <- other
        , r <- if GR.hasEdge tc (p, o) then [p]
            else if GR.hasEdge tc (o, p) then [o]
            else if o == p then [p]
            else []
        -- This condition excludes cases where `n` is the first node after
        -- `smap` and also receives other input. In such cases this would sever
        -- the collection to `smap` which we rely on to later simply drop all
        -- ctrl nodes
        -- , not (isCtrl $ fromMaybe "node not found" $ GR.lab g o)
        ]

sequentializeScalars :: (GR.DynGraph gr, gr Operator () ~ g) => (Operator -> ExecSemantic) -> g -> g
sequentializeScalars getSem g0 = foldl' f g0 (GR.topsort g0)
  where
    tc = GR.tc g0
    f g n
        | (One, One) <- getSem l
        , [(_, p)] <- ins
        , (Just (pins, _, plab, pouts), g'') <- GR.match p g'
        , One <- snd (getSem plab) =
                (ins, n, l, prune $ pouts ++ outs) GR.& ((pins, p, plab, []) GR.& g'')
        | (_, Many) <- getSem l = g
        | null prunedOuts = g
        | otherwise = (ins, n, l, prunedOuts) GR.& g'
      where
        prunedOuts = prune outs
        reachable p i = i /= p && GR.hasEdge tc (p, i)
        (Just (ins, _, l, outs), g') = GR.match n g
        prune stuff = hashNub $ [o | o@(_, o') <- stuff, not (any (flip reachable o' . snd) stuff)]


execSemOf :: (QualifiedBinding -> UDFDescription) -> Operator -> ExecSemantic
execSemOf nodes = \case
    Join {} -> (Many, Many)
    CustomOp op _
        | op == Refs.collect -> (One, Many)
        | op == Refs.smapFun -> (Many, One)
        | op == Refs.ctrl -> (One, Many)
        | QualifiedBinding ["ohua", "lang"] b <- op
        , b `elem` (["lt", "gt", "leq", "eq", "geq", "not", "and"] :: Vector Binding) -> (One, One)
        | otherwise -> execSemantic $ nodes op
    Filter {} -> (Many, Many)
    Identity -> undefined
    Project {} -> (One, One)
    Source _ -> (Many, Many)
    Sink -> (Many, Many)

-- TODO
-- - Rewrite literals to projection
-- - Incorporate indices from previously compiled udfs
annotateAndRewriteQuery ::
       ( MonadLogger m, MonadIO m )
    => GeneratedMirNodes
    -> [UDFDescription]
    -> DFGraph.OutGraph
    -> m (Gr Operator ())
annotateAndRewriteQuery gMirNodes udfs graph = do
    debugLogGR "Initial Graph" iGr
    quickDumpGrAsDot "initial-graph.dot" $ GR.nemap quickRender (const ("" :: Text)) iGr
    let s0 = (iGr, succ $ snd $ GR.nodeRange iGr)
    s1@(gr1, _) <- flip execStateT s0 $ inlineFieldAccess envInputs
    debugLogGR "Graph with nth collapsed" gr1
    quickDumpGrAsDot "nth-collapsed.dot" $ GR.nemap quickRender (const ("" :: Text)) gr1
    -- ctrlRemoved <- handleSuperfluousEdgesAndCtrl (\case CustomOp l _ -> l == Refs.ctrl; _ -> False) gr1
    -- quickDumpGrAsDot "edges-removed-graph.dot" $ GR.nemap quickRender (const ("" :: Text)) ctrlRemoved
    let udfSequentialized =
            sequentializeScalars
            (execSemOf $
             \o -> fromMaybe (error $ "Operator " <> quickRender o <> " not found in operator dictionary")
                $ HashMap.lookup o (HashMap.fromList $ map (\d -> (udfName d, d)) udfs))
            gr1
            --ctrlRemoved
    quickDumpGrAsDot "scalars-sequentialized.dot" $ GR.nemap quickRender (const ("" :: Text)) udfSequentialized
    let gr3 = multiArcToJoin2 udfSequentialized
    quickDumpGrAsDot "annotated-and-reduced-ohua-graph.dot" $ GR.nemap quickRender (const ("" :: Text)) gr3
    let gr2 = removeSuperfluousOperators gr3
    quickDumpGrAsDot "superf-removed.dot" $ GR.nemap quickRender (const ("" :: Text)) gr2
    pure gr2
    -- TODO Actually, its better to put the indices as edge labels. Means I have
    -- to group when inserting the joins, but I don't have to keep adjusting the
    -- operator Id's for the Target's
  where
    sinkId =
        maximum (0 : [unwrap operatorId | DFGraph.Operator {..} <- operators]) +
        1
    sourceNodes =
        IM.fromList $
        zip
            (hashNub
                 [ unwrap i
                 | DFGraph.Arc _ (DFGraph.EnvSource (EnvRefLit i)) <- arcs
                 ])
            [succ sinkId ..]
    iGr :: GR.Gr Operator ()
    iGr =
        GR.gmap
        (\ctx@(in_, n, lab, out) ->
             let strip = hashNub . map (first (const ()))
                 withLabel = (strip in_, n, , strip out)
             in
             withLabel $ either (retype3 gMirNodes in_) id lab
             )
        $ GR.mkGraph
            ((sinkId, Right Sink) :
             map (second (Right . Source . fromIntegral) . swap) (IM.toList sourceNodes) ++
             map
                 (\DFGraph.Operator {..} ->
                      (unwrap operatorId, Left operatorType))
                 operators) $
          ( unwrap $ DFGraph.operator $ DFGraph.returnArc graph
          , sinkId
          , (DFGraph.index $ DFGraph.returnArc graph, 0)) :
          [ (from, unwrap $ DFGraph.operator t, (outIdx, DFGraph.index t))
          | DFGraph.Arc t s' <- arcs
          , (from, outIdx) <-
                case s' of
                    DFGraph.LocalSource s ->
                        [(unwrap $ DFGraph.operator s, DFGraph.index s)]
                    DFGraph.EnvSource (EnvRefLit l) ->
                        [(sourceNodes IM.! unwrap l, 0)]
                    _ -> []
          ]
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

collapseMultiArcs :: GR.DynGraph gr => gr opLabel edgeLabel -> gr opLabel [edgeLabel]
collapseMultiArcs = GR.gmap $ (_1 %~ groupOnInt) . (_4 %~ groupOnInt)

alterLabel :: GR.DynGraph gr => GR.Node -> (l -> l) -> gr l x -> gr l x
alterLabel n f gr =
    let (Just (a, b, c, d), gr0) = GR.match n gr
    in (a, b, f c, d) GR.& gr0

inlineFieldAccess :: GetGraph g Operator () s m => LitMap -> m ()
inlineFieldAccess envInputs = do
    forNodes_
        (\case
             CustomOp op fields
                 | op == Refs.nth ->
                   case fields of
                       [(0, Left f)] -> Just $ Left f
                       s -> error $ "Nth should only have one graph input, found " <> show s
                 | op ^. namespace == ["ohua", "lang", "field"] ->
                   Just $ Right $ unwrap $ op ^. name
             _ -> Nothing) $ \node dat -> do
        [inOp] <- use $ _1 . to (flip GR.pre node)
        field <- case dat of
            Right n -> do
                pure $ Right Mir.Column { table = Just (show inOp), name = n }
            Left f ->
                let Just (0, NumericLit (fromIntegral -> idx)) =
                        find ((== 0) . view _1) $ envInputs `getLit` node in
                    pure $ Left f { outputIndex = idx }
        outs <- use $ _1 . to (flip GR.suc node)
        sDelNode node
        for_ outs $ \tOp ->
            let alteration = \case
                    Left (InternalColumn {..})
                        | producingOperator == node ->
                          if outputIndex /= 0
                          then error ("Weird index " <> show outputIndex)
                          else Just field
                    _ -> Nothing
            in do
                sInsEdge (inOp, tOp, ())
                _1 %= alterLabel tOp (alterColumns alteration)

alterColumns :: (SomeColumn -> Maybe SomeColumn) -> Operator -> Operator
alterColumns f = \case
    CustomOp b fields -> CustomOp b (map (second $ \i -> fromMaybe i $ f i) fields)
    Join j -> Join j
    Project cols -> Project (map (\i -> fromMaybe i $ f i) cols)
    Identity -> Identity
    Sink -> Sink
    Source s -> Source s
    Filter conds -> Filter $ foldr' (\(k, v) m -> maybe m (\k' -> HashMap.insert k' v $ HashMap.delete k m) $ f k) conds (HashMap.toList conds)


dropNodesRelink :: (GR.DynGraph gr, g ~ gr Operator ()) => (Operator -> Maybe GR.Node) -> g -> g
dropNodesRelink p g = foldr'
    (\(n, l) g ->
         case p l of
             Nothing -> g
             Just newNode ->
                 flip (foldr'  (\(n, f) -> alterLabel n f))
                 [ (n', alterColumns
                       (\case Left c
                                  | producingOperator c == n ->
                                    Just $ Left c {producingOperator = newNode}
                              _ -> Nothing)
                   )
                 | n' <- GR.suc g n
                 ]
                 $ GR.insEdges (map (newNode, , ()) $ GR.suc g n)
                 $ GR.delNode n g
    ) g (GR.labNodes g)

removeSuperfluousOperators :: (GR.DynGraph gr, gr Operator () ~ g) => g -> g
removeSuperfluousOperators =
    dropNodesRelink $ \case
        CustomOp o f ->
            let fromFirstInput =
                    let [(0, Left InternalColumn {..})] = f in Just producingOperator
            in
            case o of
                "ohua.lang/smapFun" -> fromFirstInput
                "ohua.lang/collect" ->
                    let Just (Left InternalColumn {..}) = Prelude.lookup 1 f in Just producingOperator
                "ohua.sql.query/group_by" -> fromFirstInput
                _ -> Nothing
        _ -> Nothing

-- mkScopeMap :: LitMap -> Gr Operator Column -> ScopeMap
-- mkScopeMap lm gr = m
--   where
--     m =
--         IM.fromList
--             [ ( n
--               , ownCtx $
--                 case pre of
--                     [] -> []
--                     _ ->
--                         maximumBy (compare `on` length) $ map (m IM.!) $
--                         map snd pre)
--             | n <- GR.nodes gr
--             , let (pre, _, label, _) = GR.context gr n
--                   ownCtx =
--                       case label of
--                           CustomOp "ohua.sql.query/group_by" _ -> (GroupBy cols :)
--                               where cols =
--                                         map
--                                             (\case
--                                                  NumericLit l ->
--                                                      (Left
--                                                           ( preNum
--                                                           , fromIntegral l))
--                                                  FunRefLit (FunRef (QualifiedBinding ["ohua", "sql", "field"] f) _) ->
--                                                      Right
--                                                          (Mir.Column Nothing $
--                                                           unwrap f)
--                                                  o ->
--                                                      error $
--                                                      "Expected numeric literal or field reference, got " <>
--                                                      quickRender o)
--                                             colNums
--                                     [(_, preNum)] = pre
--                                     colNums =
--                                         case IM.lookup n lm of
--                                             Just [(_, col)] -> [col]
--                                             cols ->
--                                                 error $
--                                                 "Expected single env argument to `group_by`, found " <>
--                                                 maybe "none" show cols
--                           -- "ohua.lang/smap" -> (SmapC :)
--                           CustomOp "ohua.lang/collect" ->
--                               \(x:xs) ->
--                                   assert
--                                       (case x of
--                                            GroupBy _ -> True
--                                            _ -> False) $
--                                   xs
--                           _ -> id
--             ]

-- retype :: GeneratedMirNodes -> Gr QualifiedBinding b -> Gr Operator b
-- retype = GR.nmap . retype2

-- retype2 :: GeneratedMirNodes -> QualifiedBinding -> Operator
-- retype2 m other@(QualifiedBinding namespace name) =
--     case namespace of
--         ["intrinsic"] ->
--             case name of
--                 "sink" -> error "No longer exists"
--                 "source" -> error "sources now need table names"
--                 _ -> error $ "Unknown intrinsic " <> showT name
--         ["ohua", "lang"]
--             | name == "(,)" -> Identity -- Needs to become a project instead
--         _ -> fromMaybe (CustomOp other []) $ HashMap.lookup other m

retype3 :: GeneratedMirNodes -> GR.Adj (Int, Int) -> QualifiedBinding -> Operator
retype3 m pre other@(QualifiedBinding namespace name) =
    case namespace of
        ["intrinsic"] ->
            case name of
                "sink" -> error "No longer exists"
                "source" -> error "sources now need table names"
                _ -> error $ "Unknown intrinsic " <> showT name
        ["ohua", "lang"]
            | name == "(,)" -> Project (map (snd . toCol) pre)
        _ -> fromMaybe (CustomOp other (map toCol pre)) $ HashMap.lookup other m
  where
    toCol ((outIdx, inIdx), op) = (inIdx ,) $ Left
        InternalColumn
        { producingOperator = op
        , outputIndex = outIdx
        }


multiArcToJoin2 :: (GR.DynGraph gr, gr Operator () ~ g) => g -> g
multiArcToJoin2 g = foldl' f g (GR.labNodes g)
  where
    f g (_, Join _) = g
    f g (n, lab) =
        case GR.pre g n of
            [] -> g
            [_] -> g
            [x, y] -> ([((), x), ((), y)], Prelude.head $ GR.newNodes 1 g, Join FullJoin, [((), n)]) GR.& GR.delEdges [(x,n), (y,n)] g
            other -> error $ "Multiple ancestors for " <> show n <> " (" <> show lab <> ") a bit unexpected " <> show other

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
                  (map (\(i, i2, s) ->
                            PP.tupled
                                [ pretty i
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

someColToMirCol :: SomeColumn -> Mir.Column
someColToMirCol =
    either (\InternalColumn {..} -> toMirCol $ DFGraph.Target (unsafeMake producingOperator) outputIndex) id

toMirCol :: DFGraph.Target -> Mir.Column
toMirCol DFGraph.Target {..} =
    Mir.Column
        { table = Nothing
        , name = showT $ "o" <> (pretty operator) <> "_i" <> (pretty index)
        }

calcColumns ::
       MonadLogger m => ScopeMap -> OperatorGraph -> m (IntMap [Either (Int, Int) Mir.Column])
calcColumns cm gr = undefined
  --   m0 <-
  --       flip execStateT initial $ for_ (GR.topsort gr) $ \self -> do
  --           let (ins, _, op, _) = GR.context gr self
  --           $(logDebug) $ "Handling " <> showT self <> " (" <> showT op <> ")"
  --           case op of
  --               Filter conds ->
  --                   case ins of
  --                       [([col], parent)] ->
  --                           forM_ (HashMap.keys conds) $
  --                           either (const $ pure ()) $ \c -> do
  --                               f <- addField parent (Left $ fst col) c
  --                               addToNode f (self, fst col) self
  --                               pure ()
  --                       _ ->
  --                           error $ "weird shape for parent of filter " <>
  --                           showT ins
  --               _ -> pure ()
  --   $(logDebug) "pre-flatten column map"
  --   $(logDebug) $ showT m0
  --   pure $
  --       IM.map
  --           (>>= \case
  --                    Left (a, b)
  --                        | null b -> [Left a]
  --                        | otherwise -> map Right b
  --                    Right c -> [Right c]) $
  --       m0
  -- where
  --   addField node col' field = do
  --       $(logDebug) $ "Adding field " <> show field <> " to " <> show node
  --       prev <- lookupField node col $ Mir.name field
  --       case prev of
  --           Nothing -> do
  --               $(logDebug) $ "No previous field " <> showT field <>
  --                   " found, escalating"
  --               escalate
  --           Just f -> do
  --               $(logDebug) $ "Previous field " <> showT f <> " found"
  --               pure f
  --     where
  --       col = either (node, ) id col'
  --       (ins, _, op, _) = GR.context gr node
  --       escalate = do
  --           fieldWithTable <-
  --               case op of
  --                   Source tidx -> do
  --                       assertM (Mir.table field == Nothing)
  --                       pure $
  --                           Mir.Column
  --                               (Just $ "&tables[" <> showT tidx <> "].clone()") $
  --                           Mir.name field
  --                   Join {} -> unimplemented
  --                   _ ->
  --                       case ins of
  --                           [([col], parent)] ->
  --                               addField
  --                                   parent
  --                                   (mapLeft (const $ fst col) col')
  --                                   field
  --                           _ ->
  --                               error $ "weird shape for parent of " <> showT op <>
  --                               " node in add column " <>
  --                               showT ins
  --           $(logDebug) $ "Found field " <> showT fieldWithTable <>
  --               " inserting with " <>
  --               showT col
  --           addToNode fieldWithTable col node
  --           $(logDebug) . showT =<< gets (IM.! node)
  --           pure fieldWithTable
  --   addToNode field col node = do
  --       s <- get
  --       put =<<
  --           lift
  --               (IM.alterF
  --                    (maybe (pure Nothing) $ fmap Just . alter (field :) col)
  --                    node
  --                    s)
  --   alter ::
  --          (MonadLogger m, Eq a, Show a, Show b, Show b1)
  --       => (b -> b)
  --       -> a
  --       -> [Either (a, b) b1]
  --       -> m [Either (a, b) b1]
  --   alter f k seq =
  --       flip evalStateT Nothing $ do
  --           s <-
  --               traverse
  --                   (\case
  --                        Left (c, l)
  --                            | c == k -> put (Just (c, f l)) $> (Left (c, f l))
  --                        other -> pure other)
  --                   seq
  --           get >>= maybe (error "not found") pure
  --           $(logDebug) $ "After `alter`: " <> show s
  --           pure s
  --   find :: Show b => (b -> Bool) -> [Either (a, [b]) b] -> Maybe b
  --   find p =
  --       (\case
  --            [f] -> Just f
  --            [] -> Nothing
  --            more -> error $ "Too many matching fields: " <> showT more) .
  --       filter p .
  --       (>>= either snd pure)
  --   lookupField ::
  --          MonadState (IntMap [Either (Column, [Mir.Column]) Mir.Column]) m
  --       => Int
  --       -> Column
  --       -> Text
  --       -> m (Maybe Mir.Column)
  --   lookupField node col f = gets (find ((== f) . Mir.name) . (IM.! node))
  --   initial :: IntMap [Either (Column, [Mir.Column]) Mir.Column]
  --   initial
  --       -- Possibly I need to add the context differently so that it registers the columns with the parents
  --    =
  --       IM.fromList
  --           [ ( node
  --             , (cm IM.! node >>= \(GroupBy c) -> map (mapLeft (, [])) c) <>
  --               map
  --                   (Left . (, []) . (node, ))
  --                   (sort $ hashNub [idx | (cols, _) <- outs, (idx, _) <- cols]))
  --           | node <- GR.nodes gr
  --           , let (_, _, _, outs) = GR.context gr node
  --           ]

toSerializableGraph2 ::
       MonadLogger m
    => [UDFDescription]
    -> ScopeMap
    -> OperatorGraph
    -> m SerializableGraph
toSerializableGraph2 udfs cm mg = do
    actualColumn <- calcColumns cm mg
    $(logDebug) "Calculated Columns"
    $(logDebug) $ showT actualColumn
    let completeOutputColsFor = map someColToMirCol . (actualColumn IM.!)
        sources =
            [ (idx, s, completeOutputColsFor s)
            | (s, Source idx) <- GR.labNodes mg
            ]
        indexMapping :: [(Word, Int)]
        indexMapping =
            zip
                [0 ..] -- new indices corresponding to index in this list
                (fst sink : -- sink node will be inserted first from noria
                 map (^. _2) (sortOn (^. _1) sources) -- then follow all base tables
                  ++
                 nonSinkSourceNodes)
        toNIdx :: Int -> Word
        toNIdx = ((IM.fromList $ map swap indexMapping) IM.!)
    adjacencies <-
        sequence
            [ (, map someColToMirCol cols, map (toNIdx . snd) ins) <$>
            case op of
                CustomOp o _ ->
                    pure $
                    Mir.Regular
                        { nodeFunction = o
                        , indices =
                              case ins of
                                  [] -> []
                                  [(edges, n)] ->
                                      map (colFrom n . fst) $ sortOn snd edges
                                  _ ->
                                      error $ "Too many ancestors for " <>
                                      showT o <>
                                      " (" <>
                                      showT ins <>
                                      ")"
                        , executionType =
                              let ctx = cm IM.! n
                               in case execSem of
                                      ReductionSem ->
                                          Mir.Reduction $ flattenCtx ctx
                                      SimpleSem ->
                                          Mir.Simple $ fromIntegral $
                                          length (flattenCtx ctx)
                                      _ -> unimplemented
                        }
                    where Just execSem = execSemMap o
                Join _ -> unimplemented
                Project _ -> unimplemented
                Identity -> pure $ Mir.Identity $ completeOutputColsFor p
                    where [(_, p)] = ins
                Sink -> error "impossible"
                Source {} -> error "impossible"
                Filter f -> do
                    conds <- traverse getCondition cols
                    pure $ Mir.Filter {conditions = conds}
                    where getCondition c =
                              case HashMap.lookup c f of
                                  Nothing
                                      | Right c <- c
                                      , cond@(Just _) <-
                                           HashMap.lookup
                                               (Right c {Mir.table = Nothing})
                                               f -> do
                                          $(logWarn) $
                                              "Condition lookup with inexact table for " <>
                                              showT c
                                          pure cond
                                  res -> pure res
            | n <- nonSinkSourceNodes
            , let (ins, _, op, _) = GR.context mg n
                  cols = actualColumn IM.! n
            ]
    let sgr =
            SerializableGraph
                { adjacencyList = adjacencies
                , sink =
                      let [(s, _, l)] = GR.inn mg $ fst sink
                       in (toNIdx s, completeOutputColsFor s)
                , sources = sources
                }
    $(logDebug) "Serializable Graph:"
    $(logDebug) $ showT sgr
    pure sgr
  where
    execSemMap :: QualifiedBinding -> Maybe ExecSemantic
    execSemMap =
        flip HashMap.lookup $ HashMap.fromList $
        map (\UDFDescription {..} -> (udfName, execSemantic)) udfs
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
    [sink] = filter (isSink . snd) (GR.labNodes mg)
    colFrom op = toMirCol . DFGraph.Target (unsafeMake op)

toSerializableGraph ::
       [UDFDescription] -> ScopeMap -> OperatorGraph -> SerializableGraph
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
                  cols =
                      case op of
                          Join {} -> cols1 <> flattenCtx ctx <> cols2 -- dirty hack
                          _
                              | null outs -> []
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
                          CustomOp o _ ->
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
                          Project _ -> unimplemented
                          Identity -> Mir.Identity $ opMap ^?! ix p . _3
                              where [(_, p)] = ins
                          Sink -> error "impossible"
                          Source {} -> error "impossible"
                          Filter f ->
                              let elems = HashMap.toList f
                               in Mir.Filter
                                      {conditions = map (Just . snd) elems}
            ]
    adjToProduced (edges, opid) = map (\(out, _) -> colFrom opid out) edges
    colFrom op = toMirCol . DFGraph.Target (unsafeMake op)
    [sink] = filter (isSink . snd) (GR.labNodes mg)
    sources =
        [ ( idx
          , s
          , map (Mir.Column (Just name) . showT) [0 .. maximum (map fst labels)])
        | (s, Source idx) <- GR.labNodes mg
        , let labels = concatMap (^. _3) $ GR.out mg s
              name = "&tables[" <> showT idx <> "].copy()" -- jikes this is dirty
        ]
    indexMapping :: [(Word, Int)]
    indexMapping =
        zip
            [0 ..] -- new indices corresponding to index in this list
            (fst sink : -- sink node will be inserted first from noria
             map (^. _2) (sortOn (^. _1) sources) -- then follow all base tables
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
    toNIdx :: Int -> Word
    toNIdx = ((IM.fromList $ map swap indexMapping) IM.!)
    scopeSize = fromIntegral . length . flattenCtx

flattenCtx :: [Scope] -> [Mir.Column]
flattenCtx = (>>= \(GroupBy l) -> map someColToMirCol l)

unimplemented :: HasCallStack => a
unimplemented = error "Function or branch not yet implemented"

noriaMirSourceDir :: IsString s => s
noriaMirSourceDir = "noria-server/mir/src"

suggestName :: NameSuggester
suggestName entryPoint =
    noriaMirSourceDir <> "/udfs/" <> unwrap (entryPoint ^. name) <> "_graph.rs"

generate :: [OperatorDescription] -> CodeGen
generate compiledNodes CodeGenData {..} = do
    let (mirNodes, udfs) =
            partitionEithers $
            map
                (\case
                     Op_MIR m -> Left m
                     Op_UDF u -> Right u)
                compiledNodes
    iGr <- annotateAndRewriteQuery (HashMap.fromList mirNodes) udfs graph
    let ctxMap = undefined
    let iGr = undefined
    debugLogGR "Annotated graph:" iGr
    tpl <- loadNoriaTemplate "udf_graph.rs"
    serializableGraph <- toSerializableGraph2 udfs ctxMap iGr
    let subs = ["graph" ~> [renderDoc $ asRust $ serializableGraph]]
    tpl' <-
        TemplateHelper.sub TemplateHelper.Opts {preserveSpace = True} tpl subs
    patchFile
        Nothing
        (noriaMirSourceDir <> "/udfs/mod.rs")
        [ "graph-mods" ~> ["mod " <> entryPointName <> "_graph;"]
        , "graph-dispatch" ~>
          [ "\"" <> entryPointName <> "\" => Some(Box::new(" <> entryPointName <>
            "_graph::mk_graph)),"
          ]
        ]
    pure $ LT.encodeUtf8 $ LT.fromStrict tpl'
  where
    entryPointName = unwrap $ entryPoint ^. name
