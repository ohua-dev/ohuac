{-# LANGUAGE TypeApplications, MultiWayIf, ConstraintKinds #-}

module Ohua.CodeGen.NoriaUDF
    ( generate
    , generateNoriaUDFs
    , FData(..)
    , AddUDF
    , GenerationType(..)
    , patchFiles
    , udfFileToPathThing
    , PathType(..)
    , noriaUdfExtraProcessing
    , parseFieldPragma
    , resolveHook
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

import Paths_ohuac

data GenerationType
    = TemplateSubstitution Template
                           FilePath
                           Substitutions
    | GenerateFile FilePath
                   Text

data FData = FData
    { generations :: [GenerationType]
    , udfName :: QualifiedBinding
    , inputBindings :: [Binding]
    , udfState :: QualifiedBinding
    , referencedFields :: [Int]
    , invokeExpr :: Expression
    }

type AddUDF = FData -> IO ()

-- | Just a simple helper to make writing the HashMap literals nicer
(~>) :: a -> b -> (a, b)
a ~> b = (a, b)

infixl 4 ~>

-- | TODO Should be `RustTyExpr` at some point
type FieldSpec = (Binding, Text)

parseFieldPragma :: Text -> FieldSpec
parseFieldPragma =
    T.break (== ':') >>> (makeThrow . T.strip *** T.strip . T.drop 1)

groupHM :: (Eq k, Hashable k) => [(k, v)] -> HashMap.HashMap k [v]
groupHM = HashMap.fromListWith (<>) . map (second pure)

expectVar :: (MonadError Error m, HasCallStack) => Expr -> m Binding
expectVar (Var v) = pure v
expectVar e = throwErrorDebugS $ "Expected var, got " <> show e

expectVarE :: HasCallStack => Expr -> Binding
expectVarE = either error id . expectVar

pattern Smap ::
        Maybe FnId -> Expression -> Expression -> Expression

pattern Smap id f coll =
        (PureFunction "ohua.lang/smap" id `Apply` f) `Apply` coll

pattern If :: Expression -> Expression -> Expression -> Expression

pattern If cond then_ else_ <-
        ((PureFunction "ohua.lang/if" _ `Apply` cond) `Apply`
           Lambda _ then_)
          `Apply` Lambda _ else_

idxPropFromName :: (Binding, Int) -> Binding
idxPropFromName (st, f) = pwu st <> makeThrow (show f) <> "__index"
  where
    pwu bnd = bnd <> "__"

resolveHook :: PreResolveHook
resolveHook ns = pure $ NS.sfImports %~ (extraSfs :) $ ns
  where
    extraSfs =
        ( OhuaFieldNS
        , [ f
          | NS.Other "declare-field" field <- ns ^. NS.pragmas
          , let (f, _) = parseFieldPragma field
          ])

-- TODO generate node struct with indices for free vars
-- TODO make sure during SSA the bindings that the ambient code in noria is going to add are renamed if they occur here
-- NOTE Assume, for the time being, there is only one state
mkMapFn ::
       (MonadGenBnd m, Monad m, MonadError Error m, MonadLogger m)
    => Fields
    -> Expression
    -> Binding
    -> Binding
    -> m (Text, Binding, [Int])
mkMapFn fields program' stateV coll = do
    logInfoN $ "Compiling udf-map function on state " <> unwrap stateV <>
        " and collection " <>
        unwrap coll <>
        "\n" <>
        quickRender program'
    freeVars <-
        filter (not . (`HashSet.member` predefVars)) <$>
        traverse expectVar (findFreeVariables program)
    unless (null freeVars) $ throwError $
        "Expected not to find free variables, found " <>
        show freeVars <>
        " in\n" <>
        quickRender program
    inLoopFieldVars <-
        traverse
            (generateBindingWith . ("ilv__" <>) . show . fst)
            loopAcessedFields
    let inLoop =
            PP.vsep $
            [ "let" <+> pretty fieldVar <+> ": &" <>
            pretty (resolveFieldType idx) <+>
            "= &" <>
            pretty rowName <>
            "[self." <>
            pretty (idxPropFromName (stateV, idx)) <>
            "].clone().into();"
            | (idx, fieldVar) <- zip fieldIndices inLoopFieldVars
            ] ++
            [toRust True program]
        inLoopFieldVarMap = IM.fromList $ zip fieldIndices inLoopFieldVars
        resolveFieldVar (from, idx)
            | from == rowName = inLoopFieldVarMap IM.! idx
            | otherwise = unsafeMake $ unwrap from <> "." <> show idx
        resolveFieldType = (fields IM.!)
        function = "let _ = " <> ppBlock inLoop <> ";"
        toRust = Ohua.CodeGen.NoriaUDF.toRust resolveFieldVar isTheState mkAc
        mkAc func' args =
            "diffs.push" <> "((Action::" <> pretty (T.toTitle (unwrap func')) <>
            (if null args || args == [Lit UnitLit]
                 then mempty
                 else PP.tupled (map (toRust False) args)) <>
            ", r_is_positive))"
    pure (renderDoc function, rowName, fieldIndices)
  where
    predefVars = HashSet.fromList [stateV, coll, rowName]
    isTheState = (== Var stateV)
    (program, rowName) =
        case program' of
            Lambda a b -> (b, a)
            _ ->
                error $ "Expected lambda as input to smap, got " <>
                quickRender program'
    fieldIndices = map fst loopAcessedFields
    loopAcessedFields = extractIndexingInto (== rowName) program

extractIndexingInto :: (Binding -> Bool) -> Expression -> [(Int, Binding)]
extractIndexingInto f program =
    hashNub
        [ (fromIntegral n, st)
        | PureFunction fun _ `Apply` Lit (NumericLit n) `Apply` _ `Apply` (expectVarE -> st) <-
              universe program
        , fun == "ohua.lang/nth"
        , f st
        ]

refBelongsToState :: a -> Bool
refBelongsToState = const True

ppBlock :: PP.Doc ann -> PP.Doc ann
ppBlock e = PP.braces (PP.line <> PP.indent 4 e <> PP.line)

expectNumLit :: Expr -> Integer
expectNumLit (Lit (NumericLit n)) = n
expectNumLit e = error $ "Expected a numeric literal, found " <> show e

-- There are some big cheats going on here in the interest of time. All
-- `ohua.lang/nth` invocations are rewritten to field access, which is true for
-- our examples, but may not always be. What i needed is actually check if the
-- thing we're calling it on is actually the row and otherwise compile to rust
-- tuple access.
toRust ::
       ((Binding, Int) -> Binding)
    -> (Expr -> Bool)
    -> (Binding -> [Expr] -> PP.Doc ann)
    -> Bool
    -> Expr
    -> PP.Doc ann
toRust resolveFieldVar isTheState mkAc isInBlock =
    \case
        Var v -> pretty v
        BindState st e -> handleBindState st e []
        If cond then_ else_ ->
            (if isInBlock
                 then id
                 else PP.parens) $
            "if" <+>
            recurse False cond <+>
            ppBlock (recurse True then_) <+>
            "else" <+>
            ppBlock (recurse True else_)
        e@(Apply _ _) ->
            case f of
                Var v -> mkFunctionCall (pretty v) args
                BindState st func -> handleBindState st func args
                Lit (FunRefLit (FunRef ref _))
                    | ref == "ohua.lang/nth" ->
                        case args of
                            [l, _, h] ->
                                pretty $
                                resolveFieldVar
                                    ( expectVarE h
                                    , fromIntegral $ expectNumLit l)
                            _ ->
                                error $
                                "Expected only one argument for field access, got " <>
                                quickRender e
                    | otherwise ->
                        case ref ^. namespace of
                            ["primitives"] ->
                                case ref ^. name of
                                    "eq" -> binop "=="
                                    "deref"
                                        | [expr] <- args ->
                                            "*" <> recurse False expr
                                        | otherwise -> wrongNumArgsErr "*" 1
                                    "divide" -> binop "/"
                                    other ->
                                        error $ "Unknown primitive function " <>
                                        unwrap other
                                where wrongNumArgsErr func num =
                                          error $
                                          "Wrong number of arguments to " <>
                                          func <>
                                          " expected " <>
                                          show num <>
                                          " got " <>
                                          show (length args)
                                      binop op
                                          | [e1, e2] <- args =
                                              recurse False e1 <+> pretty op <+>
                                              recurse False e2
                                          | otherwise = wrongNumArgsErr op 2
                            _ -> mkFunctionCall (asRust ref) args
                _ -> error $ "Unexpected type of function expression " <> show f
            where (f, args) = disassembleCall e
        l@(Lambda _ _) -> error $ "Unexpected lambda " <> quickRender l
        Let b Var {} body
            | isIgnoredBinding b -> recurse isInBlock body
        Let b e1 body ->
            (if isInBlock
                 then id
                 else ppBlock) $
            (if isIgnoredBinding b
                 then id
                 else ("let" <+> pretty b <+> "=" <+>)) $
            recurse False e1 <>
            ";" <>
            PP.line <>
            recurse True body
        Lit l ->
            case l of
                NumericLit n -> pretty n
                UnitLit -> "()"
                FunRefLit (FunRef ref _) -> asRust ref
                _ -> error $ "Unexpected literal " <> show l
  where
    recurse = toRust resolveFieldVar isTheState mkAc
    disassembleCall =
        (second reverse .) $ RS.para $ \case
            ApplyF (_, (f, args)) (arg, _) -> (f, arg : args)
            e -> (RS.embed $ fst <$> e, [])
    mkFunctionCall f args =
        f <>
        PP.tupled
            (map (recurse False) $
             if args == [Lit UnitLit]
                 then []
                 else args)
    handleBindState st func =
        case func of
            Lit (FunRefLit (FunRef ref _))
                | refBelongsToState (ref ^. namespace) && isTheState st ->
                    mkAc (ref ^. name)
                | otherwise ->
                    error $
                    "Impossible: Only one state should be in scope, found " <>
                    show st
            Var func'
                | isTheState st -> mkAc func'
                | otherwise ->
                    error $ "Multiple states and renaming aren't supported yet " <>
                    show st
            _ -> error $ "Unexpected function expression " <> quickRender func

class ToRust t where
    asRust :: t -> PP.Doc ann

instance ToRust NSRef where
    asRust = PP.hcat . intersperse "::" . map (pretty . unwrap) . unwrap

instance ToRust QualifiedBinding where
    asRust b = asRust (b ^. namespace) <> "::" <> asRust (b ^. name)

instance ToRust Binding where
    asRust = pretty . unwrap

asRustT :: ToRust a => a -> Text
asRustT = renderDoc . asRust

isIgnoredBinding :: Binding -> Bool
isIgnoredBinding b = b == "()" || "_" `T.isPrefixOf` unwrap b

mkNthExpr :: Int -> Int -> Expr -> Expr
mkNthExpr idx len tup =
    "ohua.lang/nth" `Apply` embedE idx `Apply` embedE len `Apply` tup

renderDoc :: PP.Doc a -> Text
renderDoc = PP.renderStrict . PP.layoutSmart ohuaDefaultLayoutOpts

mkReduceFn :: Applicative f => Fields -> Binding -> Expression -> f Text
mkReduceFn _ state = pure . renderDoc . (preamble <>) . go True
  where
    state' = pretty (unwrap state)
    preamble = "let" <+> state' <+> "= computer;"
    go = toRust resolveFieldVar isTheState mkAc
    isTheState = (== Var state)
    resolveFieldVar :: Show a => a -> Binding
    resolveFieldVar v =
        error $ "Field access not allowed in reduce right now. Attempted " <>
        show v
    mkAc func' args =
        state' <> "." <> pretty (unwrap func') <>
        PP.tupled
            (map (go False) $
             if args == [Lit UnitLit]
                 then []
                 else args)

newFunctionCall :: (MonadGenId m, Functor m) => QualifiedBinding -> m Expression
newFunctionCall n = PureFunction n . Just <$> generateId

asNonEmpty :: Traversal [a] [b] (NonEmpty a) [b]
asNonEmpty _ [] = pure []
asNonEmpty f (x:xs) = f (x :| xs)

processUdf ::
       (MonadOhua m)
    => Fields
    -> QualifiedBinding
    -> Expression
    -> Binding
    -> Expression
    -> m FData
processUdf fields udfName program state initState =
    case program of
        Let unit (Smap _ mapF (Var coll)) reduceF
            | isIgnoredBinding unit -> do
                (mapFn, rowName, fieldIndices) <- mkMapFn fields mapF state coll
                reduceFn <- mkReduceFn fields state reduceF
                let nodeSub =
                        TemplateSubstitution
                            "map-reduce/op.rs"
                            (noriaDataflowSourceDir <> "/ops/ohua/generated/" <>
                             toString (unwrap $ udfName ^. name) <>
                             ".rs")
                            [ "udf-name" ~>
                              [T.toTitle $ unwrap $ udfName ^. name]
                            , "udf-name-str" ~>
                              ["\"" <> unwrap (udfName ^. name) <> "\""]
                            , "map" ~>
                              ["use " <> stateNSStr <> "::Action;", mapFn]
                            , "reduce" ~> [reduceFn]
                            , "row-name" ~> [unwrap rowName]
                            , "special-state-coerce-call" ~>
                              ["." <> mkSpecialStateCoerceName udfName <> "()"]
                            , "sql-type" ~> ["SqlType::Double"] -- Do not hardcode this
                            , "node-properties" ~>
                              map
                                  (\e ->
                                       unwrap (idxPropFromName e) <> ": usize,")
                                  accessedFields
                            , "node-property-args" ~>
                              map
                                  ((<> ",") . unwrap . idxPropFromName)
                                  accessedFields
                            , "udf-args" ~> ["udf_arg_placeholder,"]
                            , "udf-args-sigs" ~> ["udf_arg_placeholder: usize,"]
                            , "udf-state-type" ~> [stateTypeStr]
                            ]
                    accessedFields = map (state, ) fieldIndices
                    stateType = getStateType initState
                    stateTypeStr = asRustT $ stateType ^. namespace
                    stateNSStr =
                        asRustT $ unwrapped @NSRef . asNonEmpty %~ init $
                        stateType ^.
                        namespace
                    stateSub =
                        TemplateSubstitution
                            "map-reduce/state.rs"
                            (noriaDataflowSourceDir <> "/state/ohua/generated/" <>
                             toString (unwrap $ udfName ^. name) <>
                             ".rs")
                            [ "state-trait-coerce-impls" ~>
                              mkStateTraitCoercionFunc
                                  udfName
                                  stateType
                                  "Option::Some(self)"
                            , "udf-state-type" ~> [stateTypeStr]
                            ]
                logDebugN $ unlines $ "Acessed fields:" : map show fieldIndices
                logInfoN $ "UDF " <> show udfName <> " callable with " <>
                    renderDoc
                        (pretty (udfName ^. name) <>
                         PP.tupled (map pretty fieldIndices))
                mkInvokeExpr <-
                    if null fieldIndices
                        then pure (`Apply` Var coll)
                        else do
                            let flen = succ $ maximum fieldIndices
                            (Endo mkFieldDestrExpr, newBnds) <-
                                fmap mconcat . for fieldIndices $ \idx -> do
                                    b <-
                                        generateBindingWith =<<
                                        make ("findex_" <> show idx)
                                    pure
                                        ( Endo $
                                          Let b (mkNthExpr idx flen (Var coll))
                                        , pure @[] b)
                            pure $ \udf ->
                                mkFieldDestrExpr
                                    (foldl' Apply udf $ map Var newBnds)
                ie <- ALang.normalize $ mkInvokeExpr $ embedE udfName
                pure
                    FData
                        { generations = [nodeSub, stateSub]
                        , udfName = udfName
                        , inputBindings = []
                        , udfState = stateType
                        , referencedFields = fieldIndices
                        , invokeExpr = ie
                        }
        _ -> error $ "Expected map-reduce pattern, got " <> quickRender program

-- HACK A dirty, dirty hack
getStateType initState =
    case [f | PureFunction f _ <- universe initState] of
        [f] -> f
        o -> error $ "Too many qualified applications in state init " <> show o

extractAcessedFields :: Expr -> [(Binding, Int)]
extractAcessedFields program =
    hashNub
        [ (expectVarE st, fromIntegral n)
        | PureFunction fun _ `Apply` Lit (NumericLit n) `Apply` _ `Apply` st <-
              universe program
        , fun == "ohua.lang/nth"
        ]

pattern OhuaFieldNS :: NSRef

pattern OhuaFieldNS <- ["ohua", "sql", "field"]
  where OhuaFieldNS = ["ohua", "sql", "field"]

data PathType
    = FilePath
    | ModPath

udfFileToPathThing :: PathType -> QualifiedBinding -> [Text] -> Text
udfFileToPathThing pt qname finalPart =
    T.intercalate sep $ pathBits <> finalPart
  where
    pathBits = map unwrap $ unwrap (qname ^. namespace) <> [qname ^. name]
    sep =
        case pt of
            FilePath -> "/"
            ModPath -> "::"

type Column = (Int, Int)

data Context =
    GroupBy [DFGraph.Target]
    -- | SmapC   -- Add this eventually
    deriving (Show)

data Operator
    = CustomOp QualifiedBinding
    | Join { joinOn :: [Context] }
    | Projection [Column]
    | Identity
    | Sink
    | Source
    deriving (Show)

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

-- TODO
-- - Rewrite literals to projection
-- - Incorporate indices from previously compiled udfs
annotateAndRewriteQuery ::
       MonadLogger m => [FData] -> DFGraph.OutGraph -> m (ContextMap, MirGraph)
annotateAndRewriteQuery compiledNodes graph = do
    debugLogGR "Initial Graph" iGr
    let s0 = (iGr, succ $ snd $ GR.nodeRange iGr)
    s1 <- flip execStateT s0 $ collapseNth envInputs
    let g = mkContextMap envInputs (fst s1)
    logInfoN $ "Context Map\n" <> show g
    (gr2, i2) <- execStateT removeSuperfluousOperators (first retype s1)
    (gr1, _, g2) <-
        flip execStateT (collapseMultiArcs gr2, i2, g) $ multiArcToJoin g
    pure (g2, gr1)
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

type LitMap = IntMap [(Int, Lit)]

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

type Rewrite a = (a -> a)

type Field1' a b = Simple Field1 a b

type Field2' a b = Simple Field2 a b

type Field3' a b = Simple Field3 a b

type Field4' a b = Simple Field4 a b

type GetGraph g a b s m
     = (MonadState s m, Field1 s s (g a b) (g a b), GR.DynGraph g)

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
             _ -> Nothing) $ \node _ -> do
        ([((0, 2), inOp)], _, _, outs) <- sGetContext node
        let [(0, NumericLit (fromIntegral -> idx))] = envInputs IM.! node
        sDelNode node
        for_ outs $ \((0, inIdx), tOp) -> sInsEdge (inOp, tOp, (idx, inIdx))

dropNodes :: GetGraph g a Column s m => (a -> Bool) -> m ()
dropNodes f =
    dropNodesProjecting
        (\n ->
             if f n
                 then Just id
                 else Nothing)

dropNodesProjecting ::
       GetGraph g a Column s m => (a -> Maybe (Int -> Int)) -> m ()
dropNodesProjecting pred = do
    mkTupNodes <- getNodesOfType (isJust . pred)
    for_ mkTupNodes $ \node -> do
        (ins, _, lab, outs) <- sGetContext node
        let inMap' =
                sortOn
                    fst
                    [ (inIdx, (outIdx, source))
                    | ((outIdx, inIdx), source) <- ins
                    ]
        assertM $ and [i == i' | (i, (i', _)) <- zip [0 ..] inMap']
        let inMap = map snd inMap'
        sDelNode node
        let Just project = pred lab
        for_ outs $ \((outIdx, inIdx), target) ->
            let (sIdx, sOp) = inMap !! project outIdx
             in sInsEdge (sOp, target, (sIdx, inIdx))

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

mkContextMap :: LitMap -> NoriaGraph QualifiedBinding Column -> ContextMap
mkContextMap lm gr = m
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

type ContextMap = IntMap [Context]

type NoriaGraph opLabel edgeLabel = GR.Gr opLabel edgeLabel

type MirGraph = NoriaGraph Operator [Column]

-- TODO Update contexts
multiArcToJoin ::
       ( a ~ Operator
       , b ~ [Column]
       , GetGraph g a b s m
       , Field2' s GR.Node
       , Field3' s ContextMap
       )
    => IntMap [Context]
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
        -- TODO update contexts
        _1 %= GR.insEdges [(p1, id, p1Cols), (p2, id, p2Cols)]
        pure (p1Cols ++ p2Cols, id)

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

toSerializableGraph :: ContextMap -> MirGraph -> SerializableGraph
toSerializableGraph cm mg =
    SerializableGraph
        { adjacencyList =
              [ (newOp, ctxCols <> cols, map toNIdx ins)
              | (_, n) <- drop 2 indexMapping
              , let (newOp, ctxCols, cols) = opMap IM.! n
                    ins = GR.pre mg n
              ]
        , sink =
              let [sink] = filter (isSink . snd) (GR.labNodes mg)
                  [(s, _, l)] = GR.inn mg $ fst sink
               in (toNIdx s, opMap ^?! ix s . _3)
        , source =
              let [src] = filter (isSource . snd) (GR.labNodes mg)
                  labels = concatMap (^. _3) $ GR.out mg (fst src)
               in map (colFrom (-1)) [0 .. maximum (map fst labels)]
        }
  where
    opMap :: IntMap (MirNode, [MirColumn], [MirColumn])
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
    contextSize = fromIntegral . length . flattenCtx

flattenCtx :: [Context] -> [MirColumn]
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

mkStateTraitCoercionFunc ::
       QualifiedBinding -> QualifiedBinding -> Text -> [Text]
mkStateTraitCoercionFunc udfName stateName impl =
    [ "fn " <> mkSpecialStateCoerceName udfName <>
      "<'a>(&'a mut self) -> Option<&'a mut SpecialStateWrapper<MemoElem<" <>
      asRustT (stateName ^. namespace) <>
      ">>> {"
    , impl
    , "}"
    ]

mkSpecialStateCoerceName :: QualifiedBinding -> Text
mkSpecialStateCoerceName udfName = "as_" <> unwrap (udfName ^. name) <> "_state"

mkOpStructName udfName = T.toTitle (unwrap $ udfName ^. name)

mkNodePath udfName = udfFileToPathThing ModPath udfName [mkOpStructName udfName]

noriaDataflowSourceDir :: IsString s => s
noriaDataflowSourceDir = "noria-server/dataflow/src"

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
patchFiles :: (MonadIO m, MonadLogger m) => Maybe FilePath -> [FData] -> m ()
patchFiles mOutDir udfs =
    mapM_ (uncurry $ patchFile mOutDir) (HashMap.toList fileMap)
  where
    toMap =
        ([ noriaDataflowSourceDir <> "/ops/ohua/mod.rs" ~>
           ["link-generated-modules" ~> ["pub mod generated;"]]
         ] <>) .
        HashMap.fromListWith (HashMap.unionWith (<>))
    fileMap = toMap $ udfs >>= mkPatchesFor

mkPatchesFor :: FData -> [(FilePath, HashMap Text [Text])]
mkPatchesFor FData {..} =
    [ noriaDataflowSourceDir <> "/ops/mod.rs" ~>
      [ "node-operator-enum" ~> [nodeOpConstr <> "(" <> nodePath <> "),"]
      , "nodeop-from-impl-macro-call" ~>
        [ "nodeop_from_impl!(NodeOperator::" <> nodeOpConstr <> ", " <> nodePath <>
          ");"
        ]
               -- nodeop_from_impl!(NodeOperator::ClickAnaUDF, ohua::click_ana::ClickAna);
      , "impl-ingredient-mut-macro" ~>
        ["NodeOperator::" <> nodeOpConstr <> "(ref mut i) => i.$fn($($arg),*),"]
                -- NodeOperator::ClickAnaUDF(ref mut i) => i.$fn($($arg),*),
      , "impl-ingredient-ref-macro" ~>
        ["NodeOperator::" <> nodeOpConstr <> "(ref i) => i.$fn($($arg),*),"]
             -- NodeOperator::ClickAnaUDF(ref i) => i.$fn($($arg),*),
      ]
    , "noria-server/dataflow/src/state/mod.rs" ~>
      [ ("state-trait-method-def" :: Text) ~>
        mkStateTraitCoercionFunc udfName udfState "Option::None"
            -- fn as_click_ana_state<'a>(&'a mut self) -> Option<&'a mut self::click_ana::ClickAnaState> {
            --     Option::None
            -- }
      ]
    , noriaDataflowSourceDir <> "/ops/ohua/att3.rs" ~>
      [ "generated-udf-inits" ~>
        [ renderDoc $ PP.dquotes (pretty udfName) <+> "=>" <+>
          ppBlock
              (PP.vsep
                   [ "assert_eq!(over_cols.len(), " <>
                     pretty (1 `max` length referencedFields) <>
                     ");"
                   , pretty
                         (mkNodePath $ udfName & namespace . unwrapped . ix 0 .~
                          "super") <>
                     "::new" <>
                     PP.tupled
                         ("parent" : "0" :
                          map
                              (\n -> "over_cols" <> PP.brackets (pretty n))
                              [0 .. pred $ length referencedFields] <>
                          ["group"])
                   ] <>
               ".into()") <>
          ","
        ]
      ]
    ]
  where
    opStructName = mkOpStructName udfName
    nodeOpConstr = T.toTitle $ opStructName <> "UDF"
    nodePath = mkNodePath udfName

pattern GenFuncsNamespace :: NSRef

pattern GenFuncsNamespace <- ["ohua", "generated"]
  where GenFuncsNamespace = ["ohua", "generated"]

type Fields = IM.IntMap Text

generateNoriaUDFs :: Fields -> AddUDF -> Expression -> OhuaM env Expression
generateNoriaUDFs fields addUdf program = do
    logInfoN $ "Complete expression for compilation\n" <> quickRender program
    program' <-
        let mempty' = mempty @(Dual (Endo Expr), HashSet.HashSet Binding)
            tellRet var = tell $ mempty' & _2 .~ HashSet.singleton var
            tellUdfE f = tell $ mempty' & _1 .~ Dual (Endo f)
            getDeps = map expectVarE . findFreeVariables
            go st (LetF v (oldExpr, expr) (extract -> body))
                | v == st =
                    error $
                    "Invariant broken, state init happened in scope for " <>
                    show st
                | otherwise = do
                    body' <- body
                    let contNormal e = _2 <>= eDeps >> pure (Let v e body')
                    (udfDeps, exprDeps) <- get
                    if exprUsesState || v `HashSet.member` udfDeps
                        then do
                            tellUdfE (Let v oldExpr)
                            _1 <>= eDeps
                            if v `HashSet.member` exprDeps
                                then if exprUsesState
                                         then tellRet v >> pure body'
                                         else contNormal oldExpr
                                else pure body'
                        else contNormal =<< expr
              where
                exprUsesState =
                    or [s == Var st | BindState s _ <- universe oldExpr]
                eDeps = HashSet.fromList $ getDeps oldExpr
            go _ e'' = RS.embed <$> traverse extract e''
         in transformM
                (\case
                     Let st initExpr body
                         | st `HashSet.member` stateVals -> do
                             logDebugN $ "Considering the function:\n" <>
                                 quickRender body
                             (e', _, (Dual (Endo mut), rets)) <-
                                 runRWST (RS.para (go st) body) () mempty
                             bnd <- generateBindingWith ("op_" <> st)
                             let udfName =
                                     QualifiedBinding GenFuncsNamespace bnd
                                 -- TODO This also necessitates changing the invoke expression to destructure this output!!
                             (v', handleReturn) <-
                                 setupReturnRecieve $ HashSet.toList rets
                             let udf = mut v'
                                 freeVars =
                                     filter (/= Var st) $ findFreeVariables udf
                             logDebugN $ "Found operator function " <>
                                 quickRender udfName <>
                                 "\n" <>
                                 quickRender (Let st initExpr udf)
                             fdata <- processUdf fields udfName udf st initExpr
                             liftIO $ addUdf fdata
                             pure $ handleReturn (invokeExpr fdata) e'
                     e -> pure e)
                program
    logDebugN $ "Remaining program\n" <> quickRender program'
    pure program'
  where
    globalVals = HashSet.fromList $ RS.cata f program
      where
        f =
            \case
                LetF b _ o -> b : o
                _ -> []
    stateVals =
        HashSet.fromList
            [ v
            | BindState st _ <- universe program
            , v <-
                  case st of
                      Var v -> [v]
                      e -> error (show e)
            ] `HashSet.difference`
        globalVals

setupReturnRecieve ::
       (Monad m, MonadGenBnd m) => [Binding] -> m (Expr, Expr -> Expr -> Expr)
setupReturnRecieve returns = do
    case returns of
        [] -> (Lit UnitLit, ) . Let <$> generateBindingWith "_"
        [i] -> pure (Var i, Let i)
        other -> do
            retBnd <- generateBindingWith "find_good_name"
            pure (mkTup, \call -> Let retBnd call . destrTup retBnd)
  where
    mkTup =
        foldl'
            Apply
            (embedE ("ohua.lang/(,)" :: QualifiedBinding))
            (map embedE returns)
    destrTup bnd =
        appEndo $
        foldMap
            (\(i, x) -> Endo $ Let x (mkNthExpr i (length returns) (Var bnd)))
            (zip [0 ..] returns)

outputFile :: MonadIO m => FilePath -> Text -> m ()
outputFile path content =
    liftIO $ do
        createDirectoryIfMissing True (FP.takeDirectory path)
        writeFile path content

doTheGenerating ::
       (MonadIO m, MonadLogger m, Foldable f)
    => (FilePath -> FilePath)
    -> f GenerationType
    -> m ()
doTheGenerating scopePath toGen = do
    templates <-
        HashMap.fromList <$>
        sequence
            [ (t, ) <$> loadNoriaTemplate t
            | TemplateSubstitution t _ _ <- Data.Foldable.toList toGen
            ]
    let getTemplate t =
            fromMaybe
                (error $ "Invariant broken, template not found " <> toText t) $
            HashMap.lookup t templates
    Data.Foldable.for_ toGen $ \case
        TemplateSubstitution t (scopePath -> path) subs ->
            outputFile path =<<
            TemplateHelper.sub
                TemplateHelper.Opts {preserveSpace = True}
                (getTemplate t)
                subs
        GenerateFile (scopePath -> path) content ->
            liftIO $ writeFile path content

loadNoriaTemplate :: MonadIO m => FilePath -> m [TemplateHelper.Rep]
loadNoriaTemplate t =
    liftIO $ do
        path <- getDataFileName $ "templates/noria" FP.</> t
        TemplateHelper.parseTemplate <$> readFile path

noriaUdfExtraProcessing ::
       (MonadError Error m, MonadIO m, MonadLogger m) => Bool -> [FData] -> m ()
noriaUdfExtraProcessing useSandbox udfs = do
    outDir <-
        if useSandbox
            then do
                fp <- liftIO $ createSysTempDir "noria-udfs"
                logInfoN
                    ("Writing files to sandbox directory " <> fromString fp)
                pure $ Just fp
            else pure Nothing
    let scopePath = maybe id (FP.</>) outDir
    doTheGenerating scopePath (udfs >>= generations)
    for_ (["ops", "state"] :: [FilePath]) $ \d ->
        outputFile
            (scopePath $ noriaDataflowSourceDir FP.</> d FP.</> "ohua/generated" FP.</>
             "mod.rs") $
        T.unlines $
        map (\u -> "pub mod " <> unwrap (udfName u ^. name) <> ";") udfs
    patchFiles outDir udfs
  where
    createSysTempDir pat =
        Temp.getCanonicalTemporaryDirectory >>= \sysd ->
            Temp.createTempDirectory sysd pat
