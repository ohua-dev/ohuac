{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

-- {-# OPTIONS_GHC -fdefer-type-errors #-}
module Ohua.CodeGen.NoriaUDF.LowerToMir
    ( generate
    , suggestName
    ) where

import Control.Lens (Simple, (%=), (^?!), ix, to, use)
import qualified Data.GraphViz as GraphViz
import qualified Data.GraphViz.Printing as GraphViz
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
import Ohua.Prelude hiding (First, Identity)
import Prelude ((!!))
import qualified Prelude
import qualified System.Directory as FS
import qualified System.FilePath as FS
import System.IO.Unsafe (unsafePerformIO)
import Text.Printf (printf)

-- data Column = InternalColumn (Int, Int) | NamedColumn Mir.Column
--     deriving (Show, Eq, Ord, Generic)
type GetGraph g a b s m
     = (MonadState s m, Field1 s s (g a b) (g a b), GR.DynGraph g)

type ScopeMap = IntMap [GScope SomeColumn]

type Gr = GR.Gr

type OperatorGraph = Gr Operator ()

type MirGraph = Gr (Mir.Node, [Mir.Column]) ()

type GeneratedMirNodes = HashMap QualifiedBinding Operator

type LitMap = IntMap [(Int, Lit)]

type AdjList a = [(a, [Mir.Column], [Word])]

data SerializableGraph =
    SerializableGraph
        { adjacencyList :: AdjList Mir.Node
        , sink :: (Word, [Mir.Column])
        , sources :: [[Mir.Column]]
        }
    deriving (Show)

type OpMap = IntMap OpMapEntry

type OpMapEntry = (Mir.Node, [Mir.Column], [Mir.Column])

type Rewrite a = (a -> a)

type Field1' a b = Simple Field1 a b

type Field2' a b = Simple Field2 a b

type Field3' a b = Simple Field3 a b

type Field4' a b = Simple Field4 a b

quickDumpGrAsDot ::
       ( GraphViz.Labellable a
       , GraphViz.Labellable b
       , GR.Graph g
       , MonadIO m
       , MonadLogger m
       )
    => Binding
    -> FilePath
    -> g a b
    -> m ()
quickDumpGrAsDot =
    \entrypoint f g -> do
        let dir = "." <> toString (unwrap entrypoint) <> "-graphs"
        i <- atomicModifyIORef' graphDumpIndex (\i -> (succ i, i))
        let file = dir FS.</> show i <> "-" <> f
        liftIO $ do
            FS.createDirectoryIfMissing False dir
            LT.writeFile file .
                GraphViz.renderDot .
                GraphViz.toDot . GraphViz.graphToDot GraphViz.quickParams $
                g
        logDebugN $ "Wrote graph " <> toText file
  where
    graphDumpIndex = unsafePerformIO $ newIORef 1
    {-# NOINLINE graphDumpIndex #-}

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
    fmap swap .
    IM.toList . IM.fromListWith (++) . fmap (second pure) . fmap swap

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

typeGraph ::
       (GR.Graph gr)
    => (Operator -> Maybe ExecSemantic)
    -> LitMap
    -> gr Operator (Int, Int)
    -> TypeMap
typeGraph udfs envInputs g = m
  where
    getType = (m IM.!)
    idxOf :: HasCallStack => Int -> NType -> NType
    idxOf i t =
        case t of
            _
                | i < 0 ->
                    error $
                    "Negative indices make no sense in this context " <>
                    show i <> " " <> quickRender t
            NTTup ts
                | Just t' <- ts ^? ix i -> t'
            NTScalar (Left InternalColumn {..})
                | outputIndex == -1 ->
                    NTScalar $
                    Left InternalColumn {producingOperator, outputIndex = i}
            _ ->
                error $
                "Cannot take index " <> show i <> " of type " <> quickRender t
    mkRetType :: GR.Node -> [NType] -> Operator -> [NType]
    mkRetType n argTypes o =
        case o of
            Filter {} -> [fromIndex Nothing 0]
            Join {} -> unexpectedOp "Join"
            Identity -> [fromIndex (Just 1) 0]
            Sink -> [fromIndex (Just 1) 0]
            Source t -> [NTSeq (NTRecFromTable $ unsafeMake $ show t)]
            Project {} -> argTypes
            CustomOp bnd _
                | bnd == Refs.nth ->
                    let Just (0, NumericLit (fromIntegral -> idx)) =
                            find ((== 0) . view _1) $ envInputs `getLit` n
                     in [fromIndex Nothing idx]
                | bnd == Refs.smapFun ->
                    case fromIndex (Just 1) 0 of
                        NTSeq t ->
                            [ t
                            , NTScalar $ Left $ InternalColumn n 1
                            , NTScalar $ Left $ InternalColumn n 2
                            ] {- is this really necessary? -}
                        _ -> invalidArgs
                | bnd == Refs.collect -> [NTSeq $ fromIndex (Just 2) 0]
                | QualifiedBinding ["ohua", "lang"] b <- bnd ->
                    case b of
                        "(,)" -> argTypes
                        "ctrl" -> Prelude.tail argTypes
                        _
                            | b `elem`
                                  (["lt", "gt", "eq", "and", "or", "leq", "geq"] :: Vector Binding) ->
                                likeUdf
                | QualifiedBinding ["ohua", "lang", "field"] f <- bnd ->
                    pure $
                    case fromIndex (Just 1) 0 of
                        NTRecFromTable t ->
                            NTScalar $
                            Right $ Mir.Column (Just $ unwrap t) $ unwrap f
                        r@(NTAnonRec _ fields) ->
                            fromMaybe
                                (error $
                                 "Field " <>
                                 unwrap f <>
                                 " not found in record " <> quickRender r) $
                            List.lookup f fields
                | Just _ <- udfs o -> likeUdf
            _ ->
                error $
                "Could not determine return type of operator " <> quickRender o
      where
        likeUdf = [NTScalar $ Left $ InternalColumn n 0]
        unexpectedOp op =
            error $ op <> "not expected here, got " <> quickRender o
        invalidArgs :: a
        invalidArgs =
            error $
            "Invalid argument types " <>
            quickRender argTypes <> " for operator " <> quickRender o
        fromIndex l i
            | Just el <- l
            , let al = length argTypes
            , el /= al =
                error $
                "Wrong number of arguments for operator " <>
                quickRender o <>
                " expected " <>
                show l <>
                " got " <> show al <> " arguments: " <> quickRender argTypes
            | Just t' <- argTypes ^? ix i = t'
            | otherwise = invalidArgs
    m =
        IM.fromList
            [ (n, (argTypes, mkRetType n argTypes l))
            | (n, l) <- GR.labNodes g
            , let argTypes =
                      map snd $
                      sortOn
                          fst
                          [ ( inIdx
                            , let retTypes = snd (getType p)
                               in if outIdx == (-1)
                                      then NTTup retTypes
                                      else fromMaybe
                                               (error $
                                                "Index too large " <>
                                                show outIdx <>
                                                " in " <>
                                                quickRender retTypes <>
                                                " in " <>
                                                quickRender (GR.lab g p) <>
                                                " from input " <>
                                                show inIdx <>
                                                " of operator " <> quickRender l) $
                                           retTypes ^? ix outIdx)
                          | (p, (outIdx, inIdx)) <- GR.lpre g n
                          ]
            ]

-- | Note that this calculates the node order once and does not update it during the fold
gFoldTopSort ::
       GR.Graph gr => (gr a b -> GR.Context a b -> gr a b) -> gr a b -> gr a b
gFoldTopSort f g =
    foldl'
        (\g' n ->
             let (Just ctx, g'') = GR.match n g'
              in f g'' ctx)
        g
        (GR.topsort g)

inlineCtrl ::
       (GR.DynGraph gr)
    => (GR.Node -> [NType])
    -> gr Operator (Int, Int)
    -> gr Operator (Int, Int)
inlineCtrl getType =
    gFoldTopSort $ \g ->
        \case
            (ins, n, CustomOp l _, outs)
                | l == Refs.ctrl ->
                    let ts = getType n
                        idxmap =
                            IM.fromList
                                [ (idx, (p, out, ts Prelude.!! idx))
                                | ((out, pred -> idx), p) <- ins
                                ]
                        (ctxSource, _, _) = idxmap IM.! (-1)
                     in flip GR.insEdges g $
                        outs >>= \((out, in_), j) ->
                            let (np, nout, t) = idxmap IM.! out
                             in case t of
                                    NTSeq _ -> [(np, j, (nout, in_))]
                                    _ ->
                                        [ (np, ctxSource, (nout, minBound))
                                        , (ctxSource, j, (maxBound, in_))
                                        ]
            ctx -> ctx GR.& g

sequentializeScalars ::
       (GR.DynGraph gr, gr Operator () ~ g)
    => (Operator -> Maybe ExecSemantic)
    -> g
    -> g
sequentializeScalars mGetSem g0 = gFoldTopSort f g0
  where
    getSem l = fromMaybe (error $ "No semantic for " <> quickRender l) $ mGetSem l
    tc = GR.tc g0
    f g' ctx@(ins, n, l, outs)
        | (One, One) <- getSem l
        , [(_, p)] <- ins
        , (Just (pins, _, plab, pouts), g'') <- GR.match p g'
        , One <- snd (getSem plab) =
            (ins, n, l, prune $ pouts ++ outs) GR.&
            ((pins, p, plab, []) GR.& g'')
        | (_, Many) <-  getSem l = g
        | null prunedOuts = g
        | otherwise = (ins, n, l, prunedOuts) GR.& g'
      where
        prunedOuts = prune outs
        reachable p i = i /= p && GR.hasEdge tc (p, i)
        g = ctx GR.& g'
        prune stuff =
            hashNub $
            [o | o@(_, o') <- stuff, not (any (flip reachable o' . snd) stuff)]

execSemOf :: (QualifiedBinding -> Maybe UDFDescription) -> Operator -> Maybe ExecSemantic
execSemOf nodes =
    \case
        Join {} -> Just (Many, Many)
        CustomOp op _
            | op == Refs.collect -> Just (One, Many)
            | op == Refs.smapFun -> Just (Many, One)
            | op == Refs.ctrl -> Just (One, Many)
            | op ^. namespace == ["ohua", "lang", "field"] -> Just (One, One)
            | QualifiedBinding ["ohua", "lang"] b <- op
            , b `elem`
                  (["lt", "gt", "leq", "eq", "geq", "not", "and"] :: Vector Binding) ->
                Just (One, One)
            | otherwise -> execSemantic <$> nodes op
        Filter {} -> Just (Many, Many)
        Identity -> Nothing
        Project {} -> Just (One, One)
        Source _ -> Just (Many, Many)
        Sink -> Just (Many, Many)

joinWhereMerge ::
       (GR.DynGraph gr, gr Operator () ~ g) => (GR.Node -> [NType]) -> g -> g
joinWhereMerge getType = \g -> foldl' f g (GR.labNodes g)
  where
    -- | If there are multiple join columns choose one, because Noria does not yet support multi condition join.
    -- This choice is ... well it looks if one of the columns mentions an `id`. Yeah, its stupid and fragile but hey...
    chooseAJoinCol = pure . maximumBy (compare `on` \(_, (c1, c2) ) -> hasId c1 $ hasId c2 0)
      where hasId = \case Right r | "id" `Text.isSuffixOf` Mir.name r -> succ; _ -> id
    f g =
        \case
            (n, Join jt []) ->
                let (Just (ins, _, jl, [((), suc)]), g') = GR.match n g
                    (Just (fins, _, filterlab@(Filter conds filterfields), fsuc), g'') =
                        GR.match suc g'
                    filtert@(NTSeq (NTRecFromTable (unwrap -> t)):_) =
                        getType suc
                    colIsFromTable =
                        \case
                            Right c -> Mir.table c == Just t
                            _ -> False
                    (rem, cols) =
                        unzip $
                        chooseAJoinCol
                            [ (sc1, (c1, c2))
                            | (sc1, Mir.Comparison Mir.Equal (Mir.ColumnValue (Right -> v))) <-
                                  HashMap.toList conds
                            , (c1, c2) <-
                                  case (colIsFromTable sc1, colIsFromTable v) of
                                      (True, False) -> [(sc1, v)]
                                      (False, True) -> [(v, sc1)]
                                      _ -> []
                            ]
                    (ng, nsuc) =
                        if length cols == HashMap.size conds
                            then (g'', fsuc)
                            else ( ( fins
                                   , suc
                                   , Filter
                                         (foldr' HashMap.delete conds rem)
                                         filterfields
                                   , fsuc) GR.&
                                   g''
                                 , [((), suc)])
                 in if length cols < 1
                        then error $
                             "No matching filters found in " <>
                             quickRender filterlab <>
                             " with type " <> quickRender filtert
                        else (ins, n, Join jt cols, nsuc) GR.& ng
            _ -> g

-- TODO
-- - Rewrite literals to projection
-- - Incorporate indices from previously compiled udfs
annotateAndRewriteQuery ::
       (MonadLogger m, MonadIO m)
    => Binding
    -> GeneratedMirNodes
    -> (Operator -> Maybe ExecSemantic)
    -> DFGraph.OutGraph
    -> m (TypeMap, Gr Operator ())
annotateAndRewriteQuery entrypoint gMirNodes getExecSemantic graph = do
    quickDumpGr "graph-with-edge-indices.dot" $
        flip GR.gmap iGr00 $ \(ins, n, l, outs) ->
            let strip = map $ first $ quickRender
             in ( strip ins
                , n
                , show n <> " " <> either quickRender quickRender l
                , strip outs)
    quickDumpGr "ctrl-removed.dot" $ printableLabelWithTypes ctrlRemoved
    debugLogGR "Initial Graph" iGr
    quickDumpGr "initial-graph.dot" $ printableLabelWithTypes iGr
    -- ctrlRemoved <- handleSuperfluousEdgesAndCtrl (\case CustomOp l _ -> l == Refs.ctrl; _ -> False) gr1
    -- quickDumpGrAsDot "edges-removed-graph.dot" $ GR.nemap quickRender (const ("" :: Text)) ctrlRemoved
    let udfSequentialized = sequentializeScalars getExecSemantic iGr
    --ctrlRemoved
    quickDumpGr "scalars-sequentialized.dot" $
        printableLabelWithTypes udfSequentialized
    let gr3 = multiArcToJoin2 udfSequentialized
    quickDumpGr "annotated-and-reduced-ohua-graph.dot" $
        mkLabelsPrintable gr3
    let gr2 = removeSuperfluousOperators gr3
    quickDumpGr "superf-removed.dot" $ printableLabelWithIndices gr2
    let whereMerged = joinWhereMerge (fst . getType) gr2
    quickDumpGr "join-where-merged.dot" $
        printableLabelWithTypes whereMerged
    pure (typeMap, whereMerged)
    -- TODO Actually, its better to put the indices as edge labels. Means I have
    -- to group when inserting the joins, but I don't have to keep adjusting the
    -- operator Id's for the Target's
  where
    quickDumpGr = quickDumpGrAsDot entrypoint
    printableLabelWithIndices ::
           (GR.DynGraph gr, PP.Pretty a) => gr a b -> gr Text Text
    printableLabelWithIndices =
        GR.gmap $ \(ins, n, l, outs) ->
            let strip = map $ first $ const ""
             in (strip ins, n, show n <> " " <> quickRender l, strip outs)
    mkLabelsPrintable :: (GR.DynGraph gr, PP.Pretty a) => gr a b -> gr Text Text
    mkLabelsPrintable = GR.nemap quickRender $ const ""
    printableLabelWithTypes ::
           (GR.DynGraph gr, PP.Pretty a) => gr a b -> gr Text Text
    printableLabelWithTypes =
        GR.gmap $ \(ins, n, l, outs) ->
            let strip = map $ first $ const ""
                tstr =
                    case mGetType n of
                        Just (int, outt) ->
                            quickRender int <> " -> " <> quickRender outt
                        Nothing -> "No type known"
             in ( strip ins
                , n
                , show n <> " " <> quickRender l <> "\n" <> tstr
                , strip outs)
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
    typeMap = typeGraph getExecSemantic envInputs iGr0
    getType n =
        fromMaybe (error $ "Type not found for node " <> show n) $ mGetType n
    mGetType = flip IM.lookup typeMap
    iGr :: GR.Gr Operator ()
    iGr = GR.emap (const ()) ctrlRemoved
    ctrlRemoved = inlineCtrl (snd . getType) iGr0
    iGr0 =
        GR.gmap
            (\ctx@(in_, n, lab, out) ->
                 let withLabel = (in_, n, , out)
                  in withLabel $
                     either (retype3 gMirNodes (fst $ getType n)) id lab)
            iGr00
    iGr00 =
        GR.mkGraph
            ((sinkId, Right Sink) :
             map
                 (second (Right . Source . fromIntegral) . swap)
                 (IM.toList sourceNodes) ++
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

collapseMultiArcs ::
       GR.DynGraph gr => gr opLabel edgeLabel -> gr opLabel [edgeLabel]
collapseMultiArcs = GR.gmap $ (_1 %~ groupOnInt) . (_4 %~ groupOnInt)

removeSuperfluousOperators :: (GR.DynGraph gr, gr Operator () ~ g) => g -> g
removeSuperfluousOperators g =
    foldr'
        (\(n, l) g ->
             let rem =
                     case l of
                         CustomOp c _
                             | QualifiedBinding ["ohua", "lang"] b <- c ->
                                 b `elem`
                                 (["smapFun", "collect", "nth"] :: Vector Binding)
                             | otherwise ->
                                 c ^. namespace == ["ohua", "lang", "field"] ||
                                 c == "ohua.sql.query/group_by"
                         _ -> False
              in if rem
                     then let [newNode] = GR.pre g n
                           in GR.insEdges (map (newNode, , ()) $ GR.suc g n) $
                              GR.delNode n g
                     else g)
        g
        (GR.labNodes g)

type TypeMap = IM.IntMap ([NType], [NType])

retype3 :: GeneratedMirNodes -> [NType] -> QualifiedBinding -> Operator
retype3 m ty other@(QualifiedBinding namespace name) =
    case namespace of
        ["intrinsic"] ->
            case name of
                "sink" -> error "No longer exists"
                "source" -> error "sources now need table names"
                _ -> error $ "Unknown intrinsic " <> showT name
        ["ohua", "lang"]
            | name == "(,)" -> Project (map toCol ty)
            | name `elem`
                  (["lt", "gt", "leq", "eq", "geq", "not", "and"] :: Vector Binding) ->
                CustomOp other (map toCol ty)
            | otherwise -> CustomOp other []
        ["ohua", "lang", "field"] -> CustomOp other []
        _ ->
            fromMaybe (CustomOp other (map toCol ty)) $
            fmap rewriteFilter $ HashMap.lookup other m
  where
    rewriteFilter a@(Filter conds vars@(st, free)) = Filter newConds vars
      where
        varnames = map unwrap $ st : free
        varmap =
            case ty of
                NTSeq stTy:rest ->
                    HashMap.fromList $ zip varnames (map handle $ stTy : rest)
                _ ->
                    error $
                    "weird type for operator " <>
                    quickRender a <> " type: " <> quickRender ty
        newConds =
            HashMap.fromList $
            map
                (\(c, cond) ->
                     ( fmap matchTable c
                     , case cond of
                           Mir.Comparison op (Mir.ColumnValue c) ->
                               Mir.Comparison
                                   op
                                   (Mir.ColumnValue $ matchTable c)
                           other -> other)) $
            HashMap.toList conds
        matchTable c@Mir.Column {..} =
            Mir.Column
                { table =
                      Just $
                      fromMaybe
                          (error $
                           "Binding " <>
                           t0 <>
                           " not found in varmap " <>
                           show varnames <> " for operator " <> quickRender a) $
                      HashMap.lookup t0 varmap
                , name
                }
          where
            t0 =
                fromMaybe
                    (error $
                     "Table missing in " <>
                     quickRender c <> " in " <> quickRender a)
                    table
        handle =
            \case
                NTRecFromTable t -> unwrap t
                _ ->
                    error $
                    "Expected table when treating " <>
                    quickRender a <> " found " <> quickRender ty
    rewriteFilter a = a
    toCol =
        \case
            NTScalar s -> s
            t ->
                error $
                "Expected scalar type, got " <>
                quickRender t <> " in operator " <> quickRender other

multiArcToJoin2 :: (GR.DynGraph gr, gr Operator () ~ g) => g -> g
multiArcToJoin2 g = foldl' f g (GR.labNodes g)
  where
    f g (_, Join {}) = g
    f g (n, lab) =
        case GR.pre g n of
            [] -> g
            [_] -> g
            [x, y] ->
                ( [((), x), ((), y)]
                , Prelude.head $ GR.newNodes 1 g
                , Join InnerJoin []
                , [((), n)]) GR.&
                GR.delEdges [(x, n), (y, n)] g
            other ->
                error $
                "Multiple ancestors for " <>
                show n <>
                " (" <> show lab <> ") a bit unexpected " <> show other

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
                  (map (\s -> "vec!" <> PP.list (encodeCols s)) $
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
                Mir.ColumnValue c -> "Value::Column" <> PP.parens (pretty c)
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
            PP.tupled [encodeOpt (\t -> "&tables" <> PP.brackets (pretty t)) table, PP.dquotes $ pretty name]
        encodeCols = map encodeCol

completeOutputColsFor :: OpMapEntry -> [Mir.Column]
completeOutputColsFor i = i ^. _2 <> i ^. _3

someColToMirCol :: SomeColumn -> Mir.Column
someColToMirCol =
    either
        (\InternalColumn {..} ->
             toMirCol $
             DFGraph.Target (unsafeMake producingOperator) outputIndex)
        id

toMirCol :: DFGraph.Target -> Mir.Column
toMirCol DFGraph.Target {..} =
    Mir.Column
        { table = Nothing
        , name = showT $ "o" <> (pretty operator) <> "_i" <> (pretty index)
        }

calcColumns ::
       (GR.Node -> [InternalColumn]) -> OperatorGraph -> IM.IntMap [SomeColumn]
calcColumns cOpOut gr = colmap
  where
    fromNode n = fromMaybe (error $ "No cols found for node " <> show n <> " in " <> show colmap) $ IM.lookup n colmap
    colmap =
        IM.fromList $
        map
            (\(n, l) ->
                 let pre = GR.pre gr n
                     fromAncestor = let [a] = pre in fromNode a
                  in (n,) $ case l of
                         Source t -> map Right $
                             fromMaybe
                                 (error $ "No columns found for " <> show t) $
                             HashMap.lookup (show t) tableColumn
                         Sink -> fromAncestor
                         CustomOp {} -> fromAncestor <> map Left (cOpOut n)
                         Project {} -> fromAncestor
                         Identity -> fromAncestor
                         Filter {} -> fromAncestor
                         Join {}
                             | length pre /= 2 -> error $ "Wrong number of ancestors " <> show (length pre) <> " on " <> show n <> " " <> quickRender l
                             | otherwise -> pre >>= fromNode

                             ) $
        GR.labNodes gr
    tableColumn =
        HashSet.toList <$>
        HashMap.fromListWith
            HashSet.union
            [ ( fromMaybe (error $ quickRender col <> " has no table") $
                Mir.table col
              , HashSet.singleton col)
            | (_, lab) <- GR.labNodes gr
            , Right col <-
                  case lab of
                      CustomOp op cols -> cols
                      Filter conds _ ->
                          HashMap.toList conds >>= \(c1, Mir.Comparison _ c2) ->
                              c1 :
                              case c2 of
                                  Mir.ColumnValue c -> [Right c]
                                  _ -> []
                      Project cols -> cols
                      Join {joinOn} -> joinOn >>= \(c1, c2) -> [c1, c2]
                      _ -> []
            ]

toSerializableGraph ::
       ( MonadLogger m, MonadIO m ) => Binding -> (Operator -> Maybe ExecSemantic) -> TypeMap -> OperatorGraph -> m SerializableGraph
toSerializableGraph entrypoint execSemMap tm mg = do
    $(logDebug) "Calculated Columns"
    $(logDebug) $ showT actualColumn
    quickDumpGrAsDot entrypoint "serializable.dot" $
        flip GR.gmap mg $ \(ins, n, l, outs) ->
            let strip = map $ first $ const ( "" :: Text )
             in (strip ins, n, show n <> " " <> quickRender l <> "\n" <> quickRender (map someColToMirCol $ actualColumn IM.! n), strip outs)
    adjacencies <-
        sequence
            [ (, map someColToMirCol cols, map (toNIdx . snd) ins) <$>
            case op of
                CustomOp o ccols ->
                    pure $
                    Mir.Regular
                        { nodeFunction = o
                        , indices = map someColToMirCol ccols
                        , executionType =
                          case execSem of
                              ReductionSem -> unimplemented
                              SimpleSem ->
                                  let [p] = ins in
                                  Mir.Simple $ fromIntegral $ length $ actualColumn IM.! snd p
                              _ -> unimplemented
                        }
                    where Just execSem = execSemMap op
                Join {joinType, joinOn }
                    | joinType /= InnerJoin -> unimplemented
                    | otherwise ->
                    let containsCols n cols = all (`elem` (actualColumn IM.! n)) cols
                        (l, r) = unzip joinOn
                        [lp, rp] = map snd ins
                        lpHasL = containsCols lp l
                        rpHasL = containsCols rp l
                        lpHasR = containsCols lp r
                        rpHasR = containsCols rp r
                        (map someColToMirCol -> left, map someColToMirCol -> right) = if
                            | lpHasL && lpHasR && rpHasR && rpHasL -> error $ "Ambiguous columns in join " <> quickRender op
                            | lpHasL && rpHasR -> (l, r)
                            | lpHasR && rpHasL -> (r, l)
                            | not (lpHasL || rpHasL) -> error $ "Left join columns not found"
                            | not (rpHasR || lpHasR) -> error $ "Right join columns not found"
                            | otherwise -> error $ "impossible " <> show (lpHasL, rpHasL, lpHasR, rpHasR)
                    in
                        pure Mir.Join { mirJoinProject = mirCols, left , right }
                Project _ -> pure $ Mir.Identity mirCols
                Identity -> pure $ Mir.Identity mirCols
                Sink -> error "impossible"
                Source {} -> error "impossible"
                Filter f _ -> do
                    conds <- traverse getCondition cols
                    pure $ Mir.Filter { conditions = map (fmap $ \(Mir.Comparison op val) -> Mir.Comparison op $ case val of
                                                                 Mir.ColumnValue v ->
                                                                     let Just c = List.elemIndex (Right v) cols
                                                                     in Mir.ColumnValue (fromIntegral c)
                                                                 Mir.ConstantValue v -> Mir.ConstantValue v
                                                         ) conds }
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
                  mirCols = map someColToMirCol cols
            ]
    let sgr =
            SerializableGraph
                { adjacencyList = adjacencies
                , sink =
                      let [(s, _, l)] = GR.inn mg $ fst sink
                       in (toNIdx s, completeOutputColsFor s)
                , sources = map (^. _3) sources
                }
    $(logDebug) "Serializable Graph:"
    $(logDebug) $ showT sgr
    pure sgr
  where
    completeOutputColsFor = map someColToMirCol . (actualColumn IM.!)
    sources = sortOn (^. _1)
        [ (idx, s, completeOutputColsFor s)
        | (s, Source idx) <- GR.labNodes mg
        ]
    indexMapping :: [(Word, Int)]
    indexMapping =
        zip
            [0 ..] -- new indices corresponding to index in this list
            (fst sink : -- sink node will be inserted first from noria
              map (^. _2) sources -- then follow all base tables
              ++
              nonSinkSourceNodes)
    toNIdx :: Int -> Word
    toNIdx = ((IM.fromList $ map swap indexMapping) IM.!)
    getUdfReturnCols n = maybe (error $ "No type for node " <> show n) (map (\case NTScalar (Left s) -> s; t -> error $ "Unexpected output of UDF " <> show n <> " " <> quickRender t) . snd ) $ IM.lookup n tm
    actualColumn = calcColumns getUdfReturnCols mg
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

unimplemented :: HasCallStack => a
unimplemented = error "Function or branch not yet implemented"
noriaMirSourceDir :: IsString s => s
noriaMirSourceDir = "noria-server/mir/src"

suggestName :: NameSuggester
suggestName entryPoint =
    noriaMirSourceDir <> "/udfs/" <> unwrap (entryPoint ^. name) <> "_graph.rs"

type UdfMap = HashMap QualifiedBinding UDFDescription

generate :: [OperatorDescription] -> CodeGen
generate compiledNodes CodeGenData {..} = do
    let (mirNodes, udfs) =
            partitionEithers $
            map
                (\case
                     Op_MIR m -> Left m
                     Op_UDF u -> Right u)
                compiledNodes
    let udfMap = HashMap.fromList $ map (\d -> (udfName d, d)) udfs
        getUdf b = HashMap.lookup b udfMap
        getExecSemantic = execSemOf getUdf
    (typeMap, iGr) <- annotateAndRewriteQuery (entryPoint ^. name) (HashMap.fromList mirNodes) getExecSemantic graph
    tpl <- loadNoriaTemplate "udf_graph.rs"
    serializableGraph <- toSerializableGraph (entryPoint ^. name) getExecSemantic typeMap iGr
    let subs = ["graph" ~> [renderDoc $ asRust $ serializableGraph]]
    tpl' <-
        TemplateHelper.sub TemplateHelper.Opts {preserveSpace = True} tpl subs
    patchFile
        Nothing
        (noriaMirSourceDir <> "/udfs/mod.rs")
        [ "graph-mods" ~> ["mod " <> entryPointName <> "_graph;"]
        , "graph-dispatch" ~>
          [ "\"" <>
            entryPointName <>
            "\" => Some(Box::new(" <> entryPointName <> "_graph::mk_graph)),"
          ]
        ]
    pure $ LT.encodeUtf8 $ LT.fromStrict tpl'
  where
    entryPointName = unwrap $ entryPoint ^. name
