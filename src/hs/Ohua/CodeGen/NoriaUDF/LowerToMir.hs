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

import Control.Lens (Simple, (?~), (%=), (^?!), ix, to, use, at)
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
import qualified Ohua.CodeGen.NoriaUDF.Paths as Path
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
        , sink :: (Word, [Mir.Column], [Mir.Column])
        , sources :: ([[Mir.Column]], [(Text, [Mir.Column])])
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
            Source t -> [NTSeq (NTRecFromTable t)]
            Project {} -> argTypes
            Union -> unexpectedOp "Union"
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
                | bnd == Refs.ctrl -> Prelude.tail argTypes
                | bnd == Refs.ifFun ->
                  case argTypes of
                      [x] -> [x,x]
                      other -> error $ "Expected only one input type to if " <> show n <> " " <> quickRender o <> ", found " <> quickRender other
                | bnd == Refs.select -> [fromIndex Nothing 1]
                | QualifiedBinding ["ohua", "lang"] b <- bnd ->
                    case b of
                        "(,)" -> argTypes
                        _
                            | b `elem`
                                  (["lt", "gt", "eq", "and", "or", "leq", "geq"] :: Vector Binding) ->
                                likeUdf
                            | otherwise ->
                                error $
                                "Unknown builtin function " <> quickRender bnd
                | QualifiedBinding ["ohua", "lang", "field"] f <- bnd ->
                    pure $
                    case fromIndex (Just 1) 0 of
                        NTRecFromTable t ->
                            NTScalar $ Right $ Mir.Column (Just t) $ unwrap f
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
       (GR.DynGraph gr, HasCallStack)
    => (GR.Node -> [NType])
    -> gr Operator (Int, Int)
    -> gr Operator (Int, Int)
inlineCtrl getType =
    gFoldTopSort $ \g ctx@(ins, n, lab, outs) ->
        let errInfo = show n <> " " <> quickRender lab in
        case lab of
            CustomOp l _
                | l == Refs.ctrl ->
                    let ts = getType n
                        idxmap =
                            IM.fromList
                                [ (idx, (p, out, ts Prelude.!! idx))
                                | ((out, pred -> idx), p) <- ins
                                ]
                        (ctxSource, ctxSourceOutIdx, _) = idxmap IM.! (-1)
                        Just ctxSourceLab = GR.lab g ctxSource
                     in case ctxSourceLab of
                            CustomOp ctxL _
                                | ctxL == Refs.smapFun ->
                                    flip GR.insEdges g $
                                    outs >>= \((out, in_), j) ->
                                        let (np, nout, t) = idxmap IM.! out
                                         in case t of
                                                NTSeq _ ->
                                                    [(np, j, (nout, in_))]
                                                _ ->
                                                    [ ( np
                                                      , ctxSource
                                                      , (nout, minBound))
                                                    , ( ctxSource
                                                      , j
                                                      , (maxBound, in_))
                                                    ]
                                | ctxL == Refs.ifFun ->
                                    let theCol =
                                            case getType ctxSource Prelude.!! ctxSourceOutIdx of
                                                NTScalar s -> s
                                                other -> error $ "Unexpected type " <> quickRender other <> " as output of `ifFn` in " <> errInfo
                                        theVal =
                                            case ctxSourceOutIdx of
                                                0 -> 1
                                                1 -> 0
                                                other ->
                                                    error $
                                                    "Unexpected if output column for node " <>
                                                    show ctxSource <>
                                                    " expected 0 or 1, got " <>
                                                    show other <>
                                                    " in " <> errInfo
                                     in ( ins
                                        , n
                                        , Filter
                                              { conditions =
                                                    [ ( theCol
                                                      , Mir.Comparison
                                                            Mir.Equal
                                                            (Mir.ConstantValue $
                                                             NumericLit theVal))
                                                    ]
                                              }
                                        , outs) GR.&
                                        g
                                | otherwise ->
                                    error $
                                    "Unexpected type (" <>
                                    quickRender ctxL <>
                                    ") for context source of node " <> errInfo
            _ -> ctx GR.& g

selectToUnion :: (GR.DynGraph gr, gr Operator (a, Int) ~ g) => g -> g
selectToUnion =
    GR.gmap $ \(ins, n, l, outs) ->
        case l of
            CustomOp o _
                | o == Refs.select ->
                    (filter (\(l, op) -> snd l == 0) ins, n, Union, outs)
            _ -> (ins, n, l, outs)

sequentializeScalars ::
       (GR.DynGraph gr, gr Operator () ~ g)
    => (Operator -> Maybe ExecSemantic)
    -> g
    -> g
sequentializeScalars mGetSem g0 = gFoldTopSort f g0
  where
    getSem = mGetSem
    tc = GR.tc g0
    f g' ctx@(ins, n, l, outs)
        | Just (One, One) <- getSem l
        , [(_, p)] <- ins
        , (Just (pins, _, plab, pouts), g'') <- GR.match p g'
        --, Just (_, One) <- getSem plab
         =
            (ins, n, l, prune $ pouts ++ outs) GR.&
            ((pins, p, plab, []) GR.& g'')
        | Just (_, Many) <- getSem l = g
        | null prunedOuts = g
        | otherwise = (ins, n, l, prunedOuts) GR.& g'
      where
        prunedOuts = prune outs
        reachable p i = i /= p && GR.hasEdge tc (p, i)
        g = ctx GR.& g'
        prune stuff =
            hashNub $
            [o | o@(_, o') <- stuff, not (any (flip reachable o' . snd) stuff)]

execSemOf ::
       (QualifiedBinding -> Maybe UDFDescription)
    -> Operator
    -> Maybe ExecSemantic
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
        Union -> Just (Many, Many)

joinWhereMerge ::
       (GR.DynGraph gr, gr Operator () ~ g) => (GR.Node -> [NType]) -> g -> g
joinWhereMerge getType = \g -> foldl' f g (GR.labNodes g)
    -- | If there are multiple join columns choose one, because Noria does not yet support multi condition join.
    -- This choice is ... well it looks if one of the columns mentions an `id`. Yeah, its stupid and fragile but hey...
  where
    chooseAJoinCol =
        pure . maximumBy (compare `on` \(_, (c1, c2)) -> hasId c1 $ hasId c2 0)
      where
        hasId =
            \case
                Right r
                    | "id" `Text.isSuffixOf` Mir.name r -> succ
                _ -> id
    f g =
        \case
            (n, Join jt []) ->
                let (Just (ins, _, jl, [((), suc)]), g') = GR.match n g
                    (Just (fins, _, filterlab@(Filter conds filterfields), fsuc), g'') =
                        GR.match suc g'
                    filtert@(NTSeq (NTRecFromTable t):_) = getType suc
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
    -> m (TypeMap, Gr Operator (), [ SomeColumn ])
annotateAndRewriteQuery entrypoint gMirNodes getExecSemantic graph = do
    quickDumpGr "graph-with-edge-indices.dot" $
        flip GR.gmap iGr00 $ \(ins, n, l, outs) ->
            let strip = map $ first $ quickRender
             in ( strip ins
                , n
                , show n <> " " <> either quickRender quickRender l
                , strip outs)
    quickDumpGr "ctrl-removed.dot" $ printableLabelWithTypes ctrlRemoved
    quickDumpGr "select-removed.dot" $ mkLabelsPrintable selectRemoved
    -- debugLogGR "Initial Graph" iGr
    quickDumpGr "initial-graph.dot" $ printableLabelWithTypes iGr
    -- ctrlRemoved <- handleSuperfluousEdgesAndCtrl (\case CustomOp l _ -> l == Refs.ctrl; _ -> False) gr1
    -- quickDumpGrAsDot "edges-removed-graph.dot" $ GR.nemap quickRender (const ("" :: Text)) ctrlRemoved
    let udfSequentialized = sequentializeScalars getExecSemantic iGr
    quickDumpGr "scalars-sequentialized.dot" $
        printableLabelWithTypes udfSequentialized
    let gr3 = multiArcToJoin2 udfSequentialized
    quickDumpGr "annotated-and-reduced-ohua-graph.dot" $ mkLabelsPrintable gr3
    let projectedCols = [ c | (_,  Project cols ) <- GR.labNodes gr3, c <- cols ]
    let gr2 =
            removeSuperfluousOperators
                (\ctx ->
                     case GR.lab' ctx of
                         CustomOp c _ ->
                             c ^. namespace == ["ohua", "lang", "field"] ||
                             c == "ohua.sql.query/group_by" ||
                             c `elem`
                             ([Refs.smapFun, Refs.collect, Refs.nth, Refs.ifFun] :: Vector QualifiedBinding)
                         Union ->
                             case length $ GR.pre' ctx of
                                 1 -> True
                                 2 -> False
                                 other ->
                                     error $
                                     "Unexpected number of ancestors for node " <>
                                     show ctx
                         Identity -> True
                         Project _ -> True
                         _ -> False)
                gr3
    quickDumpGr "superf-removed.dot" $ printableLabelWithIndices gr2
    let whereMerged = joinWhereMerge (fst . getType) gr2
    quickDumpGr "join-where-merged-with-types.dot" $
        printableLabelWithTypes whereMerged
    quickDumpGr "join-where-merged.dot" $ mkLabelsPrintable whereMerged
    pure (typeMap, whereMerged, projectedCols)
    -- TODO Actually, its better to put the indices as edge labels. Means I have
    -- to group when inserting the joins, but I don't have to keep adjusting the
    -- operator Id's for the Target's
  where
    tableEnvArgs =
        zip
            [succ $ fromMaybe sinkId $ fst <$> IM.lookupMax sourceNodes ..]
            [ (target, Source (Mir.TableByName $ unwrap t))
            | DFGraph.Arc target (DFGraph.EnvSource (FunRefLit (FunRef (QualifiedBinding ["ohua", "sql", "table"] t) _))) <-
                  arcs
            ]
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
    iGr = GR.emap (const ()) selectRemoved
    selectRemoved = selectToUnion ctrlRemoved
    ctrlRemoved = inlineCtrl (snd . getType) iGr0
    getLits n =
        fromMaybe (error $ "No literals found for node " <> show n) $
        IM.lookup n envInputs
    iGr0 =
        GR.gmap
            (\ctx@(in_, n, lab, out) ->
                 ( in_
                 , n
                 , either
                       (retype3 gMirNodes (getLits n) (fst $ getType n))
                       id
                       lab
                 , out))
            iGr00
    iGr00 =
        GR.mkGraph
            ((sinkId, Right Sink) :
             map
                 (second (Right . Source . Mir.TableByIndex . fromIntegral) .
                  swap)
                 (IM.toList sourceNodes) ++
             map
                 (\DFGraph.Operator {..} ->
                      (unwrap operatorId, Left operatorType))
                 operators ++
             map (\(idx, (_, typ)) -> (idx, Right typ)) tableEnvArgs) $
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
        ] ++
        map
            (\(idx, (t, _)) ->
                 (idx, unwrap (DFGraph.operator t), (0, DFGraph.index t)))
            tableEnvArgs
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

removeSuperfluousOperators ::
       (GR.DynGraph gr, gr a () ~ g) => (GR.Context a () -> Bool) -> g -> g
removeSuperfluousOperators p g0 =
    foldr'
        (\n g ->
             let ctx = GR.context g n
              in if p ctx
                     then let [newNode] = GR.pre' ctx
                           in GR.insEdges (map (newNode, , ()) $ GR.suc' ctx) $
                              GR.delNode n g
                     else g)
        g0
        (GR.nodes g0)

type TypeMap = IM.IntMap ([NType], [NType])

retype3 ::
       GeneratedMirNodes
    -> [(Int, Lit)]
    -> [NType]
    -> QualifiedBinding
    -> Operator
retype3 m lits ty other@(QualifiedBinding namespace name) =
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
            | name == "id" -> Identity
            | name == "unitFn" ->
                case Prelude.lookup 0 lits of
                    Just (FunRefLit (FunRef r _)) ->
                        retype3 m (error "impossible") ty r
                    other ->
                        error $
                        "An 'unitFun' should have a 'FunRefLit' as input at index 0. Instead I found these literal inputs: " <>
                        show other
            | otherwise -> CustomOp other []
        ["ohua", "lang", "field"] -> CustomOp other []
        ["ohua", "sql", "table"] -> Source (Mir.TableByName $ unwrap name)
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
        matchTable Mir.Column {table = Just (Mir.TableByName n), name} =
            Mir.Column
                { table =
                      Just $
                      fromMaybe
                          (error $
                           "Binding " <>
                           n <>
                           " not found in varmap " <>
                           show varnames <> " for operator " <> quickRender a) $
                      HashMap.lookup n varmap
                , name
                }
        matchTable c =
            error $
            "Weird shape for column in filter rewrite (must be over named table), got " <>
            quickRender c
        handle =
            \case
                NTRecFromTable t -> t
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
    f g (n, lab) =
        case lab of
            Join {} -> g
            Union -> g
            _ ->
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
            [ "adjacency_list" ~> ppVec (map toAListElem $ adjacencyList graph)
            , "sink" ~>
              let (n, proj, idxs) = sink graph
               in PP.tupled [pretty n, ppColVec proj, ppColVec idxs]
            , "sources" ~>
              PP.tupled
                  [ ppVec $ (map ppColVec $ fst $ sources graph)
                  , ppVec $
                    map (\(a, b) -> PP.tupled [PP.dquotes (pretty a) <> ".to_string()", ppColVec b]) $
                    snd $ sources graph
                  ]
            ]
      where
        ppColVec = ppVec . map encodeCol
        toAListElem (node, cols, preds) =
            PP.tupled
                [mirNodeToRust node, ppColVec cols, ppVec (map pretty preds)]
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
                          -- ppVec (map (\(a,b) -> PP.tupled [pretty a, encodeCond b] ) conditions) -- in 0.7
                          ppVec (map (encodeOpt encodeCond) conditions)
                        ]
                Mir.Regular {..} ->
                    "UDFBasic" <+>
                    recordSyn
                        [ ( "function_name"
                          , PP.dquotes (pretty nodeFunction) <> ".to_string()")
                        , ("indices", ppColVec indices)
                        , ( "execution_type"
                          , "ExecutionType::" <>
                            case executionType of
                                Mir.Reduction {..} ->
                                    "Reduction" <>
                                    recordSyn [("group_by", ppColVec groupBy)]
                                Mir.Simple i ->
                                    "Simple" <> recordSyn [("carry", pretty i)])
                        ]
                Mir.Join {..} ->
                    "Join" <+>
                    recordSyn
                        [ ("on_left", ppColVec left)
                        , ("on_right", ppColVec right)
                        , ("project", ppColVec mirJoinProject)
                        ]
                Mir.Union {..} ->
                    "Union" <+>
                    recordSyn [("emit", ppVec $ map ppColVec mirUnionEmit)]
        recordSyn =
            PP.encloseSep PP.lbrace PP.rbrace PP.comma .
            map (uncurry $ PP.surround ": ")
        ppVec l = "vec!" <> PP.list l
        encodeCol Mir.Column {..} =
            "Column::new" <>
            PP.tupled
                [ encodeOpt
                  (\case Mir.TableByIndex i -> "&tables" <> PP.brackets (pretty i);
                         Mir.TableByName n -> PP.dquotes $ pretty n)
                    table
                , PP.dquotes $ pretty name
                ]

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
    fromNode n =
        fromMaybe
            (error $
             "No cols found for node " <> show n <> " in " <> show colmap) $
        IM.lookup n colmap
    colmap =
        IM.fromList $
        map
            (\(n, l) ->
                 let pre = GR.pre gr n
                     fromAncestor =
                         let [a] = pre
                          in fromNode a
                  in (n, ) $
                     case l of
                         Source t ->
                             map Right $
                             fromMaybe
                                 (error $ "No columns found for " <> show t) $
                             HashMap.lookup t tableColumn
                         Sink -> fromAncestor
                         CustomOp {} -> fromAncestor <> map Left (cOpOut n)
                         Project {} -> fromAncestor
                         Identity -> fromAncestor
                         Filter {} -> fromAncestor
                         Union ->
                             let [a, b] = pre
                                 ret = fromNode a
                              in assert (ret == fromNode b) ret
                         Join {}
                             | length pre /= 2 ->
                                 error $
                                 "Wrong number of ancestors " <>
                                 show (length pre) <>
                                 " on " <> show n <> " " <> quickRender l
                             | otherwise -> pre >>= fromNode) $
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

instance PP.Pretty SomeColumn where
    pretty = either pretty pretty

toSerializableGraph ::
       (MonadLogger m, MonadIO m)
    => Binding
    -> (Operator -> Maybe ExecSemantic)
    -> TypeMap
    -> [SomeColumn]
    -> OperatorGraph
    -> m SerializableGraph
toSerializableGraph entrypoint execSemMap tm projectedCols mg = do
    $(logDebug) "Calculated Columns"
    $(logDebug) $ showT actualColumn
    quickDumpGrAsDot entrypoint "serializable.dot" $
        flip GR.gmap mg $ \(ins, n, l, outs) ->
            let strip = map $ first $ const ("" :: Text)
             in ( strip ins
                , n
                , show n <>
                  " " <>
                  quickRender l <>
                  "\n" <>
                  quickRender (map someColToMirCol $ actualColumn IM.! n)
                , strip outs)
    adjacencies <-
        sequence
            [ (, mirCols, map (toNIdx . snd) ins) <$>
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
                                      let [p] = ins
                                       in Mir.Simple $
                                          fromIntegral $
                                          length $ actualColumn IM.! snd p
                                  _ -> unimplemented
                        }
                    where Just execSem = execSemMap op
                Join {joinType, joinOn}
                    | joinType /= InnerJoin -> unimplemented
                    | otherwise ->
                        let containsCols actual =
                                all (`elem` actual)
                            (l, r) = unzip joinOn
                            [lp, rp] = map snd ins
                            lc = actualColumn IM.! lp
                            rc = actualColumn IM.! rp
                            lpHasL = containsCols lc l
                            rpHasL = containsCols rc l
                            lpHasR = containsCols lc r
                            rpHasR = containsCols rc r
                            (map someColToMirCol -> left, map someColToMirCol -> right) =
                                if | lpHasL && lpHasR && rpHasR && rpHasL ->
                                       error $
                                       "Ambiguous columns in join " <>
                                       quickRender op
                                   | lpHasL && rpHasR -> (l, r)
                                   | lpHasR && rpHasL -> (r, l)
                                   | not (lpHasL || rpHasL) ->
                                       error $ "Left join columns not found"
                                   | not (rpHasR || lpHasR) ->
                                       error $ "Right join columns not found"
                                   | otherwise ->
                                       error $
                                       "impossible " <>
                                       show (lpHasL, rpHasL, lpHasR, rpHasR)
                         in do
                            logDebugN $ quickRender op <> ":"
                            logDebugN $ "Saw \n    left parent " <> show lp <> "(" <> show (toNIdx lp) <> ") with columns " <> quickRender lc <> "\n    right parent " <> show rp <> "(" <> show (toNIdx rp) <> ") with columns " <> quickRender rc
                            let boolAsNot = \case True -> ""; _ -> "not "
                            logDebugN $ "Demanded left columns " <> boolAsNot lpHasL <> "found in left parent, " <> boolAsNot rpHasL <> "found in right parent"
                            logDebugN $ "Demanded right columns " <> boolAsNot lpHasR <> "found in left parent, " <> boolAsNot rpHasR <> "found in right parent"
                            logDebugN $ "Thus chosen to demand as follows:\n    from left parent (" <> show lp <> "): " <> quickRender left <> "\n    from right parent (" <> show rp <> "): " <> quickRender right
                            pure Mir.Join {mirJoinProject = mirCols, left, right}
                Union -> pure Mir.Union {mirUnionEmit = [mirCols]}
                Project _ -> unimplemented
                Identity -> pure $ Mir.Identity mirCols
                Sink -> error "impossible"
                Source {} -> error "impossible"
                Filter f _ -> do
                    let conds = map (flip HashMap.lookup $ HashMap.map reCond f) cols
                    assertM $ length (catMaybes conds) == HashMap.size f
                    pure $
                        Mir.Filter
                            { conditions = conds
                            }
                    where
                      colAsIndex :: HasCallStack => SomeColumn -> Word
                      colAsIndex c = fromIntegral $
                          fromMaybe (error $ "Expected to find column " <> quickRender c <> " in " <> quickRender cols <> "\n  Operator " <> show n <> " " <> quickRender op) $
                          List.elemIndex c cols
                      reCond (Mir.Comparison op val) =
                          Mir.Comparison op $
                          case val of
                              Mir.ColumnValue v ->
                                  Mir.ColumnValue
                                  (fromIntegral $ colAsIndex $ Right v)
                              Mir.ConstantValue v ->
                                  Mir.ConstantValue v
            | n <- nonSinkSourceNodes
            , let (ins, _, op, _) = GR.context mg n
                  cols = actualColumn IM.! n
                  mirCols = map someColToMirCol cols
            ]
    sink0 <- do
        let [(s, _, l)] = GR.inn mg $ fst sink
            avail = HashSet.fromList $ completeOutputColsFor s
        (sinkIn, sinkOut) <-
            unzip . fst <$> foldM (\(cols, m) e ->
                                 let cname = Mir.name e in
                                 case m ^? ix cname of
                                     _ | not (HashSet.member e avail) -> do
                                             logErrorN $ "Projected column " <> quickRender e <> " not found in output cols for " <> show s
                                             pure (cols, m)
                                     Just other -> do
                                         let s = maybe "_" (\case Mir.TableByName n -> n; Mir.TableByIndex i -> show i)
                                         logWarnN $ "Duplicate name of projected column " <> cname <> " rejecting " <> s (Mir.table e) <> " in favour of " <> s other
                                         pure (cols, m)
                                     Nothing -> pure (cols ++ [ (e, e { Mir.table = Just $ Mir.TableByName $ unwrap entrypoint }) ], at cname ?~ Mir.table e $ m)
                            ) ([], HashMap.empty) (map someColToMirCol projectedCols )
        pure (toNIdx s, sinkIn, sinkOut)
    let sgr =
            SerializableGraph
                { adjacencyList = adjacencies
                , sink = sink0
                , sources =
                      partitionEithers $
                      map
                          (\(idx, _, cols) ->
                               case idx of
                                   Mir.TableByIndex i -> Left cols
                                   Mir.TableByName n -> Right (n, cols))
                          sources
                }
    pure sgr
  where
    completeOutputColsFor = map someColToMirCol . (actualColumn IM.!)
    sources =
        sortOn
            (view _1)
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
    toNIdx = ((IM.fromListWith (\a _ -> error $ "Double index " <> show a) $ map swap indexMapping) IM.!)
    getUdfReturnCols n =
        maybe
            (error $ "No type for node " <> show n)
            (map (\case
                      NTScalar (Left s) -> s
                      t ->
                          error $
                          "Unexpected output of UDF " <>
                          show n <> " " <> quickRender t) .
             snd) $
        IM.lookup n tm
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

-- isIsomorphic :: (Eq a, Ord b) => Gr a b -> Gr a b -> Bool
-- isIsomorphic gr1 gr2 = isJust $ isomorphicMapping gr1 gr2

-- isomorphicMapping :: (Eq a, Ord b) => Gr a b -> Gr a b -> Maybe IsoMap
-- isomorphicMapping g1 g2 = either (const Nothing) Just $ matchGraph g1 g2

-- type IsoMap = IntMap.IntMap Int

-- maxOn :: Ord b => (a -> b) -> a -> a -> a
-- maxOn f a0 a1
--     | ((>=) `on` f) a0 a1 = a0
--     | otherwise = a1

-- type IsoFailData = (IsoMap, Maybe (Int, Int))

-- plusEither ::
--        Either IsoFailData b -> Either IsoFailData b -> Either IsoFailData b
-- plusEither (Left a) (Left a2) = Left $ maxOn (IntMap.size . fst) a a2
-- plusEither r@(Right _) _ = r
-- plusEither _ b = b

-- emptyEither :: Either IsoFailData b
-- emptyEither = Left (mempty, Nothing)

-- sumEither ::
--        (Container c, Element c ~ Either IsoFailData b)
--     => c
--     -> Either IsoFailData b
-- sumEither = foldl' plusEither emptyEither

-- mapsEither ::
--        Container c
--     => (Element c -> Either IsoFailData b)
--     -> c
--     -> Either IsoFailData b
-- mapsEither f = foldl' (\a b -> plusEither a (f b)) emptyEither

-- matchGraph :: (Eq a, Ord b) => Gr a b -> Gr a b -> Either IsoFailData IsoMap
-- matchGraph gr1 gr2
--     | order gr1 == 0 && order gr2 == 0 = Right mempty
-- matchGraph gr1 gr2 = go (nodes gr1) [] [] mempty
--   where
--     go :: [Int] -> [Int] -> [Int] -> IsoMap -> Either IsoFailData IsoMap
--     go rest !gr1Selected !gr2Selected !mapping =
--         if gr1Subgr == rename mapping (subgraph gr2Selected gr2)
--             then descend rest
--             else failMatch
--       where
--         gr1Subgr = subgraph gr1Selected gr1
--         descend []
--             | gr1Subgr == gr1 && order gr2 == order gr1Subgr = Right mapping
--             | otherwise = failMatch
--         descend (x:xs) = selectX `mapsEither` nodes gr2
--           where
--             selectX k =
--                 go xs (x : gr1Selected) (k : gr2Selected) $
--                 IntMap.insert k x mapping
--         failMatch = Left (lastMapping, lastSelects)
--         lastSelects =
--             case (gr1Selected, gr2Selected) of
--                 (x:_, k:_) -> Just (k, x)
--                 _ -> Nothing
--         lastMapping = maybe id (IntMap.delete . fst) lastSelects mapping
--     rename mapping gr = mkGraph ns es
--       where
--         ns = first newName <$> labNodes gr
--         es = map (\(a, b, c) -> (newName a, newName b, c)) (labEdges gr)
--         newName node =
--             fromMaybe
--                 (error $
--                  "Invariant broken: missing mapping for node " <> show node) $
--             IntMap.lookup node mapping

unimplemented :: HasCallStack => a
unimplemented = error "Function or branch not yet implemented"

suggestName :: NameSuggester
suggestName entryPoint =
    Path.udfsDir <> "/" <> unwrap (entryPoint ^. name) <> "_graph.rs"

type UdfMap = HashMap QualifiedBinding UDFDescription

fromSerializableGraph :: SerializableGraph -> Gr (Either Operator Mir.Node) ()
fromSerializableGraph SerializableGraph{..} =
    GR.mkGraph
    (map (second fst) adj)
    [ (fromIntegral from, to, ()) | (to, ( _, others )) <- adj, from <- others]
  where
    adj = zip [0..] $
        (Left Sink, [fromIntegral $ sink ^. _1]) :
        map ((, []) . Left . Source . Mir.TableByIndex . fst) (zip [0..] $ fst sources) ++
        map ((, []) . Left . Source . Mir.TableByName . fst) (snd sources) ++
        [ (Right n, others)
        | (n, _, others) <- adjacencyList
        ]

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
    (typeMap, iGr, projectedCols) <-
        annotateAndRewriteQuery
            (entryPoint ^. name)
            (HashMap.fromList mirNodes)
            getExecSemantic
            graph
    tpl <- loadNoriaTemplate "udf_graph.rs"
    serializableGraph <-
        toSerializableGraph (entryPoint ^. name) getExecSemantic typeMap projectedCols iGr
    quickDumpGrAsDot (entryPoint ^. name) "reconstituted-serializable.dot"
        $ GR.gmap (\(ins, n, l, outs) ->
            let strip = map $ first $ const ( "" :: Text )
             in ( strip ins
                , n
                , show n <> " " <> either quickRender show l
                , strip outs))
        $ fromSerializableGraph serializableGraph
    let subs = ["graph" ~> [renderDoc $ asRust $ serializableGraph]]
    tpl' <-
        TemplateHelper.sub TemplateHelper.Opts {preserveSpace = True} tpl subs
    patchFile
        Nothing
        Path.udfsModFile
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
