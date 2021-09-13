{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

-- {-# OPTIONS_GHC -fdefer-type-errors #-}
module Ohua.CodeGen.NoriaUDF.LowerToMir
    ( makeGraph
    , graphToSubs
    , SerializableGraph
    ) where

import Control.Lens (Simple, (?~), (%=), (^?!), ix, to, use, at)
import qualified Control.Lens as Lens
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
    , renderDoc
    )
import Ohua.CodeGen.NoriaUDF.Types
import qualified Ohua.DFGraph as DFGraph
import qualified Ohua.Helpers.Graph as GR
import qualified Ohua.Helpers.Template as TemplateHelper
import Ohua.Prelude hiding (First, Identity, (&))
import Prelude ((!!))
import qualified Prelude
import qualified System.Directory as FS
import qualified System.FilePath as FS
import System.IO.Unsafe (unsafePerformIO)
import Text.Printf (printf)
import qualified Control.Exception (throw, displayException)
import qualified GHC.Exception


data LoweringError
    = UnexpectedTypeForField NType Binding
    | UnknownBuiltin QualifiedBinding
    | MissingReturnType Operator
    | IncorrectType Text QualifiedBinding GR.Node [NType]
    | FieldNotFound Binding Binding NTFields
    | UnexpectedOperator Operator
    | InvalidIndexIntoType Int NType
    | InvalidIndexIntoTypes Int [NType] Operator Int Operator
    | ExpectedNumericLiteral Lit
    | InvalidArgumentType GR.Node Operator (Maybe (Int, Int)) [NType]
    | LabelNotFound Int
    | InvalidReturnType Operator [NType] (Maybe Int)
    | UnexpectedOutputColumn Operator Int Int
    | FilterIsMissingAField
    | InvalidLiteralInputs Operator [Lit]
    | BindingNotFoundInVarmap Operator Text (HashMap Text Mir.Table)
    | UnexpectedColumnType Mir.Column
    | UnexpectedType Text Operator [NType]
    | TypeNotKnown GR.Node
    | LiteralNotFound GR.Node
    | WrongNumberOfAncestors GR.Node Operator Int Int
    | ColumnNotFound GR.Node (IM.IntMap LoweringMapEntry)
    | TableColumnsNotFound Mir.Table (HashMap Mir.Table [Mir.Column])
    | InputsDoNotLineUp [(Int, Lit)] [NType]
    | InvalidFilterAfterIsEmpty GR.Node (GR.MContext Operator ())
    | UnexpectedNumberOfAncestors GR.Node Operator Word [GR.Node]
    | AmbiguousColumnsInJoin Operator
    | JoinColumnsNotFound Bool Operator [SomeColumn] [SomeColumn] [SomeColumn]
    | Impossible
    | Unimplemented
    | ExpectedEqualType GR.Node Operator NType NType
    | ColumnHasNoTable Mir.Column
    | ColumnNotFoundInList SomeColumn [SomeColumn] GR.Node Operator
    | InvalidUDFReturnType GR.Node NType
    | Expected2TypeRowsInSelect GR.Node SelectPayload
    | CannotReconcileSelectArmTypes (Either SomeColumn Mir.Table) (Either SomeColumn Mir.Table)
    | AncestorNotFound [Int] GR.Node GR.Node
    | NoMirEquivalent Operator GR.Node
    | UnableToFindSingleMatchingCtrlChild GR.Node [(GR.Node, Maybe Operator)]
    | WeirdProjectSetupInLeftOuterJoinIf GR.Node [(GR.Node, [ProjectColSpec])] [GR.Node]
    deriving Show

data ErrorWithTrace = forall e . Exception e => ErrorWithTrace CallStack e

instance Exception ErrorWithTrace

instance Prelude.Show ErrorWithTrace where
    show (ErrorWithTrace trace e) =
        Prelude.unlines [Control.Exception.displayException e, "Stack Trace:", GHC.Exception.prettyCallStack trace]

throw :: ( HasCallStack, Exception e) => e -> a
throw e = Control.Exception.throw $ ErrorWithTrace callStack e

traceWarning :: Text -> a -> a
traceWarning t = trace ("WARNING: " <> t)

instance Exception LoweringError

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

type AdjList a = [Adj a]
type Adj a = (a, [Mir.Column], [Word])

data SerializableGraph =
    SerializableGraph
        { adjacencyList :: AdjList Mir.Node
        , sink :: (Word, [Mir.Column], [Mir.Column])
        , sources :: ([[Mir.Column]], [(Text, [Mir.Column])])
        }
    deriving (Show, Eq, Generic)


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
            exists <- FS.doesDirectoryExist dir
            when (exists && i == initial) $ FS.removeDirectoryRecursive dir
            FS.createDirectoryIfMissing False dir
            LT.writeFile file .
                GraphViz.renderDot .
                GraphViz.toDot . GraphViz.graphToDot GraphViz.quickParams $
                g
        logDebugN $ "Wrote graph " <> toText file
  where
    initial = 1
    graphDumpIndex = unsafePerformIO $ newIORef initial
    {-# NOINLINE graphDumpIndex #-}

expectNumLit :: HasCallStack => Lit -> Integer
expectNumLit (NumericLit n) = n
expectNumLit other = throw $ ExpectedNumericLiteral other

getLit :: IntMap [a] -> Int -> [a]
getLit m k = fromMaybe [] $ IM.lookup k m

isJoin, isSink, isSource :: Operator -> Bool
isJoin = \case
    Join {} -> True
    _ -> False

isSink = \case
    Sink -> True
    _ -> False

isSource = \case
    Source {} -> True
    _ -> False

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
                | i < 0 -> throw $ InvalidIndexIntoType i t
            NTTup ts
                | Just t' <- ts ^? ix i -> t'
            NTScalar (Left InternalColumn {..})
                | outputIndex == -1 ->
                    NTScalar $
                    Left InternalColumn {producingOperator, outputIndex = i}
            _ -> throw $ InvalidIndexIntoType i t
    mkRetType :: GR.Node -> [(Int , NType )] -> Operator -> [NType]
    mkRetType n indexedArgTypes o =
        case o of
            IsEmptyCheck -> [NTScalar (Left InternalColumn {producingOperator=n,outputIndex=0})]
            Filter {} -> [fromIndex Nothing 0]
            Join {} -> throw $ UnexpectedOperator o
            Identity -> [fromIndex (Just 1) 0]
            Sink -> [fromIndex (Just 1) 0]
            Source t -> [NTSeq (NTRecFromTable t)]
            Project {..} -> [NTTup $ map (NTScalar . either (Left . fst ) id ) projectEmit]
            Select _ ->
                  case argTypes of
                      [_, x] -> [x]
                      [_, a, b]
                          | shallowEqNType a b -> [a]
                          | Just t <- (if | isUnitNType a -> Just b | isUnitNType b -> Just a | otherwise -> Nothing) -> [t]
                          | Just (t1, t2) <-
                            (if | isSeqNType a -> Just (a, b) | isSeqNType b -> Just (b, a) | otherwise -> Nothing) ->
                                traceWarning ("select arguments had differing type, choosing sequence type " <> quickRender t1 <> " over " <> quickRender t2) [t1]
                          | otherwise -> throw $ ExpectedEqualType n o a b
                      _ -> throw $ InvalidArgumentType n o (Just (2, length argTypes)) argTypes
            Ctrl {} -> Prelude.tail argTypes
            CustomOp bnd _
                | bnd == Refs.nth ->
                    let (0, NumericLit (fromIntegral -> idx)) = fromMaybe (throw $ LiteralNotFound n) $
                            find ((== 0) . view _1) $ envInputs `getLit` n
                     in case fromIndex (Just 1) 0 of
                            NTTup tys
                                | Just t <- tys ^? ix idx -> [t]
                            t -> throw (InvalidIndexIntoType idx t)
                | bnd == Refs.smapFun ->
                    case fromIndex (Just 1) 0 of
                        NTSeq t ->
                            [ t
                            , NTScalar $ Left $ InternalColumn n 1
                            , NTScalar $ Left $ InternalColumn n 2
                            ] {- is this really necessary? -}
                        _ -> invalidArgs
                | bnd == Refs.collect -> [NTSeq $ fromIndex (Just 2) 1]
                | bnd == Refs.ctrl -> throw $ UnexpectedOperator o
                | bnd == Refs.ifFun ->
                  case argTypes of
                      [x] -> [x,x]
                      _ -> throw $ IncorrectType "expected one onput type" Refs.ifFun n argTypes
                | QualifiedBinding ["ohua", "lang"] b <- bnd ->
                    case b of
                        "(,)" -> [NTTup argTypes ]
                        _
                            | b `elem`
                                  (["lt", "gt", "eq", "and", "or", "leq", "geq", "<", ">", "<=", ">=", "==", "!=", "&&", "||"] :: Vector Binding) ->
                                likeUdf
                            | otherwise -> throw $ UnknownBuiltin bnd
                | QualifiedBinding ["ohua", "lang", "field"] f <- bnd ->
                    pure $
                    case fromIndex (Just 1) 0 of
                        NTRecFromTable t ->
                            NTScalar $ Right $ Mir.Column (Just t) $ unwrap f
                        r@(NTAnonRec rb fields) ->
                            fromMaybe
                                (throw $ FieldNotFound f rb fields) $
                            List.lookup f fields
                        other -> throw $ UnexpectedTypeForField other f
                | Just _ <- udfs o -> likeUdf
            _ -> throw $ MissingReturnType o
      where
        argTypes = map snd indexedArgTypes
        likeUdf = [NTScalar $ Left $ InternalColumn n 0]
        invalidArgs :: a
        invalidArgs = throw $ InvalidArgumentType n o Nothing argTypes
        fromIndex (Just el) _
            | let al = length argTypes
            , el /= al = throw $ InvalidArgumentType n o (Just (el, al)) argTypes
        fromIndex _ i
            | Just t' <- argTypes ^? ix i = t'
            | otherwise = throw $ InvalidArgumentType n o (Just (i, length argTypes)) argTypes
    m =
        IM.fromList
            [ (n, (map snd argTypes, mkRetType n argTypes l))
            | (n, l) <- GR.labNodes g
            , let argTypes =
                      sortOn
                          fst
                          [ ( inIdx
                            , let retTypes = snd (getType p)
                               in if outIdx == (-1)
                                      then NTTup retTypes
                                      else fromMaybe
                                               (throw $ InvalidIndexIntoTypes outIdx retTypes (getLabel g p) inIdx l) $
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

getLabel :: GR.Graph gr => gr a b -> Int -> a
getLabel g n = fromMaybe (throw $ LabelNotFound n) $ GR.lab g n

handleCtrl :: (GR.DynGraph gr) => gr Operator () -> gr Operator ()
handleCtrl = flip GR.ufold GR.empty $ \ctx g ->
    case GR.lab' ctx of
        Ctrl _ IfCtrl {..} ->
            (_3 .~
            Filter
            { conditions =
                    [ ( conditionColumn
                      , Mir.Comparison
                          Mir.Equal
                          (Mir.ConstantValue
                              $ if iAmTrueBranch then 1 else 0))
                    ]
            , arguments = ("what?", []) -- throw FilterIsMissingAField
            }) ctx & g
        _ -> ctx & g


inlineCtrl ::
       (GR.DynGraph gr, HasCallStack)
    => (GR.Node -> [NType])
    -> gr Operator (Int, Int)
    -> gr Operator (Int, Int)
inlineCtrl getType =
    gFoldTopSort $ \g ctx@(ins, n, lab, outs) ->
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
                        ctxSourceLab = getLabel g ctxSource
                        g' =
                            case ctxSourceLab of
                                CustomOp ctxL _
                                    | ctxL == Refs.smapFun -> g
                                    | ctxL == Refs.ifFun ->
                                        let theCol =
                                                case getType ctxSource Prelude.!! ctxSourceOutIdx of
                                                    NTScalar s -> s
                                                    other -> throw $ InvalidReturnType lab [other] (Just n)
                                            theVal =
                                                case ctxSourceOutIdx of
                                                    0 -> 1
                                                    1 -> 0
                                                    other -> throw $ UnexpectedOutputColumn lab n other
                                        in ( ins
                                            , n
                                            , Filter
                                                  { conditions =
                                                        [ ( theCol
                                                          , Mir.Comparison
                                                                Mir.Equal
                                                                (Mir.ConstantValue
                                                                theVal))
                                                        ]
                                                  , arguments = ("what?", []) -- throw FilterIsMissingAField
                                                  }
                                            , outs) GR.& g
                                _ -> throw $ UnexpectedOperator ctxSourceLab
                    in  flip GR.insEdges g' $
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
            _ -> ctx GR.& g

dropASelectInput :: (GR.DynGraph gr, gr Operator (a, Int) ~ g) => g -> g
dropASelectInput =
    GR.gmap $ \(ins, n, l, outs) ->
        case l of
            Select {} ->
                (filter ((==0) . snd . fst) ins, n, l, outs)
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
    canInline l = l == IsEmptyCheck || Just (One, One) == getSem l
    f g' ctx@(ins, n, l, outs)
        | canInline l
        , [(_, p)] <- ins
        , (Just (pins, _, plab, pouts), g'') <- GR.match p g'
        --, Just (_, One) <- getSem plab
         =
            (ins, n, l, prune $ pouts ++ outs) GR.&
            ((pins, p, plab, []) GR.& g'')
        | Just (_, Many) <- getSem l = g
        | CustomOp fun _ <- l
        , False
        , Refs.smapFun == fun || Refs.ifFun == fun =
          (hashNub [p | p@(_, p0) <- ins,  not $ any (reachable p0 . snd) ins], n, l, prunedOuts) GR.& g'
        | null prunedOuts = g
        | otherwise = (ins, n, l, prunedOuts) GR.& g'
      where
        prunedOuts = prune outs
        reachable p i = i /= p && GR.hasEdge tc (p, i)
        g = ctx GR.& g'
        prune stuff =
            hashNub $
            [o | o@(_, o') <- stuff, not (any (flip reachable o' . snd) stuff)]

builtinSimpleFuns :: Vector Binding
builtinSimpleFuns = ["nth", "lt", "gt", "leq", "eq", "geq", "not", "and", "==", ">=", "<=", "!=", "<", ">", "&&", "||"]

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
            , b `elem` builtinSimpleFuns -> Just (One, One)
            | otherwise -> execSemantic <$> nodes op
        Filter {} -> Just (Many, Many)
        Identity -> Nothing
        Project {} -> Just (One, One)
        Source _ -> Just (Many, Many)
        Sink -> Just (Many, Many)
        Select {} -> Just (Many, Many)
        IsEmptyCheck -> Just (Many, One)
        Ctrl {} -> Just (Many, One)

(&) :: GR.DynGraph gr => GR.Context a b -> gr a b -> gr a b
(&) = (GR.&)

infixr 4 &

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
    handleJoin g n jt
        | length cols < 1 = throw $ UnexpectedType "no matching filter found" filterlab filtert
        | [( (), fsuc' )] <- fsuc
        , (Just (_, _, IsEmptyCheck, emouts), g3) <- GR.match fsuc' g2 =
                let [f1, f2] = map snd emouts
                    matchFilter v (Just ([], _, Ctrl op ( IfCtrl {..}), outs))
                        | iAmTrueBranch == v -- && op == fsuc'    The previous op has already been dropped. but this would be a good safety condition
                        = outs
                    matchFilter _ ctx = throw $ InvalidFilterAfterIsEmpty fsuc' ctx in
                let (matchFilter True -> f1outs, g4) = GR.match f1 g3
                    (matchFilter False -> f2outs, g5) = GR.match f2 g4
                    (( theCol, _ ):_) = cols
                    mkFilter op = Filter { conditions = HashMap.fromList [(theCol, Mir.Comparison op (Mir.ConstantValue Mir.None) )]
                                         , arguments = ("no", []) -- throw FilterIsMissingAField
                                         }
                in (ins, n, Join LeftOuterJoin $ map swap cols, [((), f1 ), ((), f2)]) &
                   ([], f1, mkFilter Mir.Equal, f1outs ) &
                   ([], f2, mkFilter Mir.NotEqual, f2outs ) &
                   g5
        | otherwise = (ins, n, Join jt cols, nsuc) GR.& ng
      where
        (Just (ins, _, _, [((), suc)]), g1) = GR.match n g
        (Just (fins, _, filterlab@(Filter conds filterfields), fsuc), g2) =
            GR.match suc g1
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
                then (g2, fsuc)
                else ( ( fins
                        , suc
                        , Filter
                              (foldr' HashMap.delete conds rem)
                              filterfields
                        , fsuc) GR.&
                        g2
                      , [((), suc)])
    f g =
        \case
            (n, Join jt []) -> handleJoin g n jt
            _ -> g

mergeSmapToCtrl :: (GR.DynGraph gr) => gr Operator () -> gr Operator ()
mergeSmapToCtrl = \g -> foldl' f g (GR.labNodes g)
  where
    f g (n, CustomOp o _)
        | o == Refs.smapFun =
              case matching of
                  -- Sometimes an smap has no ctrl (if there were no free
                  -- variables). So we insert one. I don't like that we have to
                  -- do that but I don't see a way around this.
                  [] -> (_3 .~ Ctrl n SmapCtrl) ctx & g'
                  [( ctrl, _ )] ->
                      GR.insEdges (map (, ctrl, ()) $ GR.pre g n) $
                      GR.insEdges (map ( (ctrl, , ()) . fst ) others) $
                      GR.delNode n g
                  _ -> throw $ UnableToFindSingleMatchingCtrlChild n labSuc
      where
        (Just ctx, g') = GR.match n g
        labSuc = map (id &&& GR.lab g) $ GR.suc g n
        (matching, others) =
            List.partition
            (\(_, l) ->
                    case l of
                        Just (Ctrl src _) -> src == n
                        _ -> False)
            labSuc
    f g _ = g


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
    quickDumpGr "select-removed.dot" $ mkLabelsPrintable selectRemoved
    -- debugLogGR "Initial Graph" iGr
    quickDumpGr "initial-graph.dot" $ printableLabelWithTypes iGr
    let smapRemoved = mergeSmapToCtrl iGr
    quickDumpGr "smap-removed.dot" $ printableLabelWithTypes smapRemoved
    -- ctrlRemoved <- handleSuperfluousEdgesAndCtrl (\case CustomOp l _ -> l == Refs.ctrl; _ -> False) gr1
    -- quickDumpGrAsDot "edges-removed-graph.dot" $ GR.nemap quickRender (const ("" :: Text)) ctrlRemoved
    let udfSequentialized = sequentializeScalars getExecSemantic smapRemoved
    quickDumpGr "scalars-sequentialized.dot" $
        printableLabelWithTypes udfSequentialized
    let gr3 = multiArcToJoin2 udfSequentialized
    quickDumpGr "annotated-and-reduced-ohua-graph.dot" $ mkLabelsPrintable gr3
    let gr2 =
            removeSuperfluousOperators
                (\ctx ->
                     case GR.lab' ctx of
                         Ctrl _ SmapCtrl -> assert (length (GR.pre' ctx) == 1) True
                         CustomOp c _ ->
                             c ^. namespace == ["ohua", "lang", "field"] ||
                             c == "ohua.sql.query/group_by" ||
                             c `elem`
                             ([Refs.smapFun, Refs.collect, Refs.nth, Refs.ifFun] :: Vector QualifiedBinding)
                         s@Select {} ->
                             case length $ GR.pre' ctx of
                                 1 -> True
                                 2 -> False
                                 _ -> throw $ UnexpectedNumberOfAncestors (GR.node' ctx) s 2 (GR.pre' ctx)
                         Identity -> True
                         _ -> False)
                gr3
    quickDumpGr "superf-removed.dot" $ printableLabelWithIndices gr2
    let whereMerged = joinWhereMerge (fst . getType) gr2
    quickDumpGr "join-where-merged-with-types.dot" $
        printableLabelWithTypes whereMerged
    quickDumpGr "join-where-merged.dot" $ mkLabelsPrintable whereMerged
    lojOptimized <- optimizeLeftOuterJoin whereMerged
    quickDumpGr "loj-optimized.dot" $ mkLabelsPrintable lojOptimized
    let ctrlHandled = handleCtrl lojOptimized
    quickDumpGr "ctrl-handled.dot" $ mkLabelsPrintable ctrlHandled
    pure (typeMap, ctrlHandled)
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
        fromMaybe (throw $ TypeNotKnown n) $ mGetType n
    mGetType = flip IM.lookup typeMap
    iGr :: GR.Gr Operator ()
    iGr = GR.emap (const ()) selectRemoved
    selectRemoved = dropASelectInput ctrlRemoved
    ctrlRemoved = {- inlineCtrl (snd . getType) -} iGr0
    getLits n =
        fromMaybe [] $
        IM.lookup n envInputs
    iGr0 =
        GR.gmap
            (\(in_, n, lab, out) ->
                 ( in_
                 , n
                 , either
                       (retype3 gMirNodes iGr0 n (getLits n) (fst $ getType n))
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

removeSuperfluousOperators ::
       (GR.DynGraph gr, gr a () ~ g, a ~ Operator) => (GR.Context a () -> Bool) -> g -> g
removeSuperfluousOperators p g0 =
    foldr'
        (\n g ->
             let ctx = GR.context g n
              in if p ctx
                     then let newNode = case GR.pre' ctx of
                                            [n] -> n
                                            other -> throw $ UnexpectedNumberOfAncestors n (GR.lab' ctx) 1 other
                           in GR.insEdges (map (newNode, , ()) $ GR.suc' ctx) $
                              GR.delNode n g
                     else g)
        g0
        (GR.nodes g0)

type TypeMap = IM.IntMap ([NType], [NType])

optimizeLeftOuterJoin :: ( GR.DynGraph gr, gr Operator () ~ g, MonadLogger m ) => g -> m g
optimizeLeftOuterJoin = \g -> foldM f g (GR.labNodes g)
  where
    f g (joinN, Join { joinType = LeftOuterJoin, ..} )
        | all isSimple thenLabels
        , all (== Mir.None) litMatches
        , all fromParentTable litMatchCols =
          pure $
          GR.insEdges [(joinN, List.head $ GR.suc g elseCtrl, ())
                      , (List.head $ filter (not . (`elem` thenNodes)) $ GR.pre g selectN , List.head $ GR.suc g selectN, ())] $
          GR.delNodes thenNodes $
          GR.delNodes [thenCtrl, elseCtrl, selectN] g
        | otherwise = mapM_ @[_] logDebugN
          [ "Could not optimize join " <> show joinN
          , "\tNodes are simple: " <> show (all isSimple thenLabels) <> " " <> show thenLabels
          , "\tLiterals are None: " <> show (all (==Mir.None) litMatches) <> " " <> show litMatches
          , "\tMAtching columns are from parent " <> show (all fromParentTable litMatchCols) <> " " <> show litMatchCols
          , "\tLeft project: " <> show lproject
          , "\tRight project: " <> show rproject
          , "\tJoin Columns: " <> show joinOn
          ] >> pure g
      where
        ( litMatches, litMatchCols ) = unzip $ mapMaybe (\case (Left (_, dat ), Right c) -> Just (dat, c); _ -> Nothing) $ zip (snd lproject ) (snd rproject)
        (lproject, rproject) =
            let go n = let Just l = GR.lab g n in
                    case l of
                        Project {projectEmit} -> (n, projectEmit)
                        _ -> let [p] = GR.pre g n in go p
            in case map go $ GR.pre g selectN of
                [l@(ln, _), r@(rn, _)]
                    | ln `elem` thenNodes -> (l, r)
                    | rn `elem` thenNodes -> (r, l)
                found -> throw $ WeirdProjectSetupInLeftOuterJoinIf selectN found thenNodes
        ( [ thenCtrl ], [ elseCtrl ] ) = List.partition
            (\case (GR.lab g -> Just (Filter {conditions})) | [(_, Mir.Comparison op (Mir.ConstantValue Mir.None))] <- HashMap.toList conditions -> op == Mir.Equal -- should probably also amke sure the column is correct
                   _ -> False) $ GR.suc g joinN
        ((selectN, selectL), ( thenNodes, thenLabels ) ) =
            let go n = let Just l = GR.lab g n in
                    case l of
                        Select {} -> ((n, l), [])
                        _ -> (s, (n, l): others ++ ( more >>= snd ))
                            where (s, others): more = map go $ GR.suc g n
            in second (unzip . Prelude.tail) $ go thenCtrl
        fromParentTable = case joinOn of
            [(_, Right Mir.Column{table=Just t})] -> \case
                Right Mir.Column{table=Just t'} -> t' == t
                _ -> False
            _ -> const False
        isSimple = \case
            CustomOp b _ -> ( b ^.namespace ) `elem` ( [ ["ohua", "lang", "field"] ] :: Vector NSRef)
            Project {} -> True
            _ -> False
    f g _ = pure g

determineCtrlType :: GR.Graph gr => gr Operator (Int, Int) -> GR.Node -> [NType] -> (Int, CtrlType )
determineCtrlType g n ts = (ctxSource, ) $
    case ctxSourceLab of
        CustomOp ctxL _
            | ctxL == Refs.smapFun -> SmapCtrl
            | ctxL == Refs.ifFun -> flip IfCtrl theCol $
                  case ctxSourceOutIdx of
                      0 -> True
                      1 -> False
                      other -> throw $ UnexpectedOutputColumn lab n other
        _ -> throw $ UnexpectedOperator ctxSourceLab
  where
    lab = CustomOp Refs.ctrl []
    theCol =
        case ts of
            NTScalar s:_ -> s
            other -> throw $ InvalidReturnType lab other (Just n)
    idxmap =
        IM.fromList
        [ (idx, (p, out, ts Prelude.!! idx))
        | (p, (out, pred -> idx)) <- GR.lpre g n
        ]
    (ctxSource, ctxSourceOutIdx, _) = idxmap IM.! (-1)
    ctxSourceLab = getLabel g ctxSource

retype3 :: (GR.Graph gr, g ~ gr Operator (Int, Int))
    => GeneratedMirNodes
    -> g
    -> GR.Node
    -> [(Int, Lit)]
    -> [NType]
    -> QualifiedBinding
    -> Operator
retype3 m g n lits ty other@(QualifiedBinding namespace name) =
    case namespace of
        ["intrinsic"] ->
            case name of
                "sink" -> throw $ UnexpectedOperator Sink
                _ -> throw $ UnknownBuiltin other
        ["ohua", "lang"] ->
            case name of
                "(,)" ->
                    Project
                    { projectEmit = map (mapLeft (first $ \idx -> InternalColumn { producingOperator = n, outputIndex = idx}) ) consolidated
                    --, projectLits = map (\( idx, l ) -> (, litToDBLit l)) lits
                    }
                "nth" -> CustomOp other []
                "ctrl" -> uncurry Ctrl $ determineCtrlType g n ty
                _ | name `elem` builtinSimpleFuns ->
                    CustomOp other mkUDFInputs
                "id" -> Identity
                "select" ->
                    let flattenTy = Lens.para $ \a r -> case a of
                            NTScalar s -> [Left s]
                            NTRecFromTable t -> [Right t]
                            _ -> concat r
                        (_:ts) = ty
                    in
                        Select $ map flattenTy ts
                "unitFn"
                    | Just (FunRefLit (FunRef r _)) <- Prelude.lookup 0 lits ->
                          retype3 m g n (error "impossible") ty r
                    | otherwise -> throw $ InvalidLiteralInputs (CustomOp other []) (map snd lits)
                _ -> CustomOp other []
        ["ohua", "lang", "field"] -> CustomOp other []
        ["ohua", "sql", "table"] -> Source (Mir.TableByName $ unwrap name)
        ["ohua", "sql", "query"] | name == "table_is_empty" -> IsEmptyCheck
        _ ->
            fromMaybe (CustomOp other mkUDFInputs) $
            fmap rewriteFilter $ HashMap.lookup other m
  where
    mkUDFInputs = map (mapLeft snd) consolidated
    consolidated = unfoldr consolidate (sortOn fst lits, ty, 0)
    consolidate (lits, tys, succ -> n) = case lits of
        []
            | t:ts <- tys -> Just (Right $ toCol t, ([], ts, n) )
            | otherwise -> Nothing
        (li,l):ls
            | succ li == n -> Just (Left (li, litToDBLit l), (ls, tys, n))
            | t:ts <- tys -> Just (Right $ toCol t, (lits, ts, n))
            | otherwise -> throw $ InputsDoNotLineUp lits tys
    rewriteFilter a@(Filter conds vars@(st, free)) = Filter newConds vars
      where
        varnames = map unwrap $ st : free
        varmap =
            case ty of
                NTSeq stTy:rest ->
                    HashMap.fromList $ zip varnames (map handle $ stTy : rest)
                _ -> throw $ InvalidReturnType a ty Nothing
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
        matchTable = \case
            Mir.Column {table = Just (Mir.TableByName n), name} ->
                Mir.Column
                    { table =
                          Just $
                          fromMaybe
                              (throw $ BindingNotFoundInVarmap a n varmap) $
                          HashMap.lookup n varmap
                    , name
                    }
            c -> throw $ UnexpectedColumnType c
        handle =
            \case
                NTRecFromTable t -> t
                _ -> throw $ UnexpectedType "NTRecFromTable" a ty
    rewriteFilter a = a
    toCol =
        \case
            NTScalar s -> s
            t -> throw $ UnexpectedType "NTScalar" (CustomOp other []) [t]
    litToDBLit = \case
        FunRefLit (FunRef (QualifiedBinding ["ohua", "sql", "query"] "NULL") _) -> Mir.None
        other -> throw $ InvalidLiteralInputs (Project []) [other]

multiArcToJoin2 :: (GR.DynGraph gr, gr Operator () ~ g) => g -> g
multiArcToJoin2 g = foldl' f g (GR.labNodes g)
  where
    f g (n, lab) =
        case lab of
            Join {} -> g
            Select _ -> g
            _ ->
                fst $ foldl (\(g, other) x -> (maybe id (\y g ->
                                                               ( [((), x), ((), y)]
                                                               , Prelude.head $ GR.newNodes 1 g
                                                               , Join InnerJoin []
                                                               , [((), n)]) GR.&
                                                               GR.delEdges [(x, n), (y, n)] g
                                                       ) other g
                                             , Just x))  (g, Nothing) (GR.pre g n)

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
                Mir.Int n -> "Int" <> PP.parens (pretty n)
                Mir.None -> "None"
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
                        , ("indices", ppVec $ map encodeValue indices)
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
                    (if isLeftJoin then "LeftJoin" else "Join" ) <+>
                    recordSyn
                        [ ("on_left", ppColVec left)
                        , ("on_right", ppColVec right)
                        , ("project", ppColVec mirJoinProject)
                        ]
                Mir.Union {..} ->
                    "Union" <+>
                    recordSyn [("emit", ppVec $ map ppColVec mirUnionEmit)]
                Mir.Project {..} ->
                    "Project" <+>
                    recordSyn
                    [ ("emit", ppColVec projectEmit)
                    , ("arithmetic", ppVec [])
                    , ("literals", ppVec $ map (\(s, c) -> PP.tupled [ PP.dquotes ( pretty s ) <> ".to_string()", encodeValueConstant c]) projectLiterals )
                    ]
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


instance PP.Pretty SomeColumn where
    pretty = either pretty pretty

type LoweringMapEntry = (Mir.Node, [SomeColumn], [GR.Node])

handleNode :: (Operator -> Maybe ExecSemantic) -> (IM.IntMap ([NType], [NType] )) -> GR.Gr Operator () -> IM.IntMap LoweringMapEntry -> GR.Node -> LoweringMapEntry
handleNode execSemMap tm mg m n = case op of
    CustomOp o ccols ->
        withCols (fromAncestor <> map Left (getUdfReturnCols n)) $
        defaultRet
        Mir.Regular
            { nodeFunction = o
            , indices = map (either Mir.ConstantValue (Mir.ColumnValue . colAsIndex) ) ccols
            , executionType =
                  case execSem of
                      ReductionSem -> unimplemented
                      SimpleSem ->
                          let [p] = ins
                            in Mir.Simple $
                              fromIntegral $
                              length $ ancestorColumns (snd p)
                      _ -> unimplemented
            }
        where Just execSem = execSemMap op
    Join {joinType, joinOn}
        | [lp,rp] <- map snd ins ->
              let lc = ancestorColumns lp
                  rc = ancestorColumns rp
                  lpHasL = containsCols lc l
                  rpHasL = containsCols rc l
                  lpHasR = containsCols lc r
                  rpHasR = containsCols rc r
                  leftStuff = (lp, lc)
                  rightStuff = (rp, rc)
                  (( left, leftCol ), ( right, rightCol )) =
                      if | lpHasL && lpHasR && rpHasR && rpHasL ->
                              throw $ AmbiguousColumnsInJoin op
                          | lpHasL && rpHasR -> (leftStuff, rightStuff)
                          | lpHasR && rpHasL -> (rightStuff, leftStuff)
                          | not (lpHasL || rpHasL) ->
                                throw $ JoinColumnsNotFound True op l lc rc
                          | not (rpHasR || lpHasR) ->
                                throw $ JoinColumnsNotFound False op l lc rc
                          | otherwise ->
                                throw $ Impossible
                  proj = leftCol <> rightCol
          in withCols proj $
              withAncestors [left, right] $
              defaultRet Mir.Join
              { mirJoinProject = map someColToMirCol proj
              , left = map someColToMirCol l
              , right = map someColToMirCol r
              , isLeftJoin = joinType == LeftOuterJoin
              }
        | otherwise ->
              throw $ WrongNumberOfAncestors n op 2 (length ins)
      where
        (l, r) = unzip joinOn
        containsCols actual =
            all (`elem` actual)
    Select tys
        | [t1, t2] <- tys ->
          let
              (HashSet.fromList -> fromL, HashSet.fromList -> fromR) = unzip $ zip t1 t2 >>= \case
                  (Left c, Left c2) -> pure (c, c2)
                  (Right tab, Right tab2)
                      | tab == tab2 -> map (\(Right -> a) -> (a, a)) $ tableColumn ^?! ix tab
                  (t1, t2) -> throw $ CannotReconcileSelectArmTypes t1 t2
              fromArms = HashSet.union fromL fromR
              extraA = HashSet.difference retASet fromArms
              extraB = HashSet.difference retBSet fromArms
              extra = HashSet.intersection extraA extraB
              emitL = filter (flip HashSet.member (HashSet.union extra fromL) ) retA
          in
          assert (length t1 == length t2) $
          withCols emitL $
          defaultRet Mir.Union
          { mirUnionEmit = map (map someColToMirCol)
            [ emitL, filter (flip HashSet.member (HashSet.union extra fromR)) retB
            ]
          }
        | otherwise -> throw $ Expected2TypeRowsInSelect n tys
      where
        (a, b) = case pre of
                    [a,b] -> (a,b)
                    other -> throw $ UnexpectedNumberOfAncestors n op 2 other
        retA = ancestorColumns a
        retASet = HashSet.fromList retA
        retB = ancestorColumns b
        retBSet = HashSet.fromList retB

    Project {..} ->
        withCols (fromAncestor <> map (Left . fst) projectLits) $
        defaultRet Mir.Project
        { projectEmit = map someColToMirCol fromAncestor
        , projectLiterals = zip (repeat "unused") $ map snd projectLits
        }
      where projectLits = mapMaybe (\case Left l -> Just l; _ -> Nothing) projectEmit
    Identity -> defaultRet $ Mir.Identity $ map someColToMirCol fromAncestor
    Filter f _ ->
        defaultRet
            Mir.Filter
                { conditions = map (flip HashMap.lookup $ HashMap.map reCond f) fromAncestor
                }
      where
        reCond (Mir.Comparison op val) =
            Mir.Comparison op $
            case val of
                Mir.ColumnValue v ->
                    Mir.ColumnValue
                    (fromIntegral $ colAsIndex $ Right v)
                Mir.ConstantValue v ->
                    Mir.ConstantValue v
    IsEmptyCheck -> withCols [Left $ InternalColumn {producingOperator=n, outputIndex=0}] $ defaultRet $ throw $ NoMirEquivalent IsEmptyCheck n
    Source t ->
        let cols =
                map Right $
                fromMaybe
                    (throw $ TableColumnsNotFound t tableColumn) $
                HashMap.lookup t tableColumn
        in withCols cols $ defaultRet $ throw $ NoMirEquivalent (Source t) n
    Sink -> defaultRet $ throw $ NoMirEquivalent Sink n
    other -> throw $ UnexpectedOperator other
  where
    colAsIndex :: HasCallStack => SomeColumn -> Word
    colAsIndex c = fromIntegral $
        fromMaybe (throw $ ColumnNotFoundInList c fromAncestor n op) $
        List.elemIndex c fromAncestor
    pre = GR.pre mg n
    fromAncestor =
        let a = case pre of
                    [a] -> a
                    other -> throw $ UnexpectedNumberOfAncestors n op 1 other
        in ancestorColumns a
    ancestorColumns :: HasCallStack => GR.Node -> [SomeColumn]
    ancestorColumns n0 = fromMaybe (throw $ AncestorNotFound (IM.keys m) n n0) $ m ^? ix n0 . _2
    defaultRet = ( , fromAncestor , map snd ins)
    withCols c = _2 .~ c
    withAncestors c = _3 .~ c
    (ins, _, op, _) = GR.context mg n
    getUdfReturnCols n =
        maybe
            (throw $ TypeNotKnown n)
            (map (\case
                      NTScalar (Left s) -> s
                      t -> throw (InvalidUDFReturnType n t)) .
             snd) $
        IM.lookup n tm
    tableColumn =
        HashSet.toList <$>
        HashMap.fromListWith
            HashSet.union
            [ ( fromMaybe (throw $ ColumnHasNoTable col) $
                Mir.table col
              , HashSet.singleton col)
            | (_, lab) <- GR.labNodes mg
            , Right col <-
                  case lab of
                      CustomOp op cols -> rights cols
                      Filter conds _ ->
                          HashMap.toList conds >>= \(c1, Mir.Comparison _ c2) ->
                              c1 :
                              case c2 of
                                  Mir.ColumnValue c -> [Right c]
                                  _ -> []
                      Project {..} -> mapMaybe (\case Right r -> Just r ; _ -> Nothing) projectEmit
                      Join {joinOn} -> joinOn >>= \(c1, c2) -> [c1, c2]
                      _ -> []
            ]

toSerializableGraph ::
       (MonadLogger m, MonadIO m)
    => Binding
    -> (Operator -> Maybe ExecSemantic)
    -> TypeMap
    -> OperatorGraph
    -> m SerializableGraph
toSerializableGraph entrypoint execSemMap tm mg = do
    $(logDebug) "Calculated Columns"
    quickDumpGrAsDot entrypoint "serializable.dot" $
        flip GR.gmap mg $ \(ins, n, l, outs) ->
            let strip = map $ first $ const ("" :: Text)
             in ( strip ins
                , n
                , show n <>
                  " " <>
                  quickRender l <>
                  "\n" <>
                  quickRender (completeOutputColsFor n)
                , strip outs)

    let adjacencies =
            [ _2 %~ map someColToMirCol $ _3 %~ map toNIdx $ (loweredOps IM.! n)
            | n <- nonSinkSourceNodes
            ]
    sink0 <- do
        let [(s, _, _)] = GR.inn mg $ fst sink
            avail = HashSet.fromList $ completeOutputColsFor s
            projectedCols = HashSet.toList $ findProjCols s
            findProjCols s =
                case GR.lab mg s of
                    Just (Project p) -> HashSet.fromList $ rights p <> mapMaybe (\case Left (l,_) -> Just $ Left l; _ -> Nothing) p
                    Just _ -> HashSet.unions $ map findProjCols $ GR.pre mg s
                    Nothing -> error "Why no label?"
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
    loweredOps = IM.fromList
                 [ (n, handleNode execSemMap tm mg loweredOps n)
                 | n <- GR.nodes mg
                 ]
    completeOutputColsFor n = loweredOps ^?! ix n . _2 . to (map someColToMirCol)
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
            (map (^. _2) sources -- base tables come first
              ++
             nonSinkSourceNodes)
    toNIdx :: Int -> Word
    toNIdx = ((IM.fromListWith (\a _ -> error $ "Double index " <> show a) $ map swap indexMapping) IM.!)
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
unimplemented = throw Unimplemented

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

descriptiveCommentsForSerializableGraph :: SerializableGraph -> [Text]
descriptiveCommentsForSerializableGraph g =
    [ renderDoc $ "//" <+> pretty i <+> PP.brackets (PP.concatWith (PP.surround ", ") (map pretty t )) <+> pretty n
    | (i, (n,_,t)) <- zip [(length $ sources g ^. _2)..] $ adjacencyList g
    ]

makeGraph :: (MonadLogger m, MonadIO m ) => [OperatorDescription] -> CodeGenData -> m SerializableGraph
makeGraph compiledNodes CodeGenData {..} = do
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
    (typeMap, iGr) <-
        annotateAndRewriteQuery
            (entryPoint ^. name)
            (HashMap.fromList mirNodes)
            getExecSemantic
            graph
    toSerializableGraph (entryPoint ^. name) getExecSemantic typeMap iGr

graphToSubs g = descriptiveCommentsForSerializableGraph g <> [renderDoc $ asRust $ g]
