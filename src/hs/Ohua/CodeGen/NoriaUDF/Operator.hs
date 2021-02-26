{-# LANGUAGE TypeApplications, MultiWayIf, ConstraintKinds #-}

module Ohua.CodeGen.NoriaUDF.Operator
    ( generateOperators
    , OperatorDescription(..)
    , UDFDescription(..)
    , RegisterOperator
    , GenerationType(..)
    , patchFiles
    , udfFileToPathThing
    , PathType(..)
    , extraOperatorProcessing
    , ToRust(..)
    , (~>)
    , loadNoriaTemplate
    , renderDoc
    , patchFile
    , ExecSem(..)
    , ExecSemantic
    , pattern SimpleSem
    , pattern ReductionSem
    , rewriteQueryExpressions
    , mainArgsToTableRefs
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
import System.Directory (makeAbsolute)
import qualified System.IO.Temp as Temp

import Ohua.ALang.Lang
import Ohua.ALang.PPrint (ohuaDefaultLayoutOpts, quickRender)
import qualified Ohua.ALang.Passes as ALang (normalize)
import qualified Ohua.ALang.Refs as ALang
import Ohua.ALang.Util (findFreeVariables, fromApplyToList, fromListToApply)
import Ohua.CodeGen.Iface
import qualified Ohua.CodeGen.JSONObject as JSONObject
import qualified Ohua.DFGraph as DFGraph
import qualified Ohua.Frontend.NS as NS
import qualified Ohua.Helpers.Graph as GR
import Ohua.Helpers.Template (Substitutions, Template)
import qualified Ohua.Helpers.Template as TemplateHelper
import Ohua.CodeGen.NoriaUDF.Util
import Ohua.CodeGen.NoriaUDF.QueryEDSL (queryEDSL)
import qualified Ohua.CodeGen.NoriaUDF.Mir as Mir
import Ohua.CodeGen.NoriaUDF.Types

import Paths_ohuac


type Fields = IM.IntMap Text



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

pattern Nth n len coll <-
        ((PureFunction "ohua.lang/nth" _ `Apply` Lit (NumericLit n))
           `Apply` Lit (NumericLit len))
          `Apply` coll

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

pattern ReductionSem :: ExecSemantic

pattern ReductionSem = (Many, One)

pattern SimpleSem :: ExecSemantic

pattern SimpleSem = (One, One)

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
            loopAccessedFields
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
        toRust =
            Ohua.CodeGen.NoriaUDF.Operator.toRust
                resolveFieldVar
                isTheState
                mkAc
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
            Lambda a b -> (dropUnusedFieldAccess b, a)
            _ ->
                error $ "Expected lambda as input to smap, got " <>
                quickRender program'
    fieldIndices = map fst loopAccessedFields
    loopAccessedFields = extractIndexingInto (== rowName) program

dropUnusedFieldAccess :: Expression -> Expression
dropUnusedFieldAccess =
    rewrite $ \case
        Let bnd (Nth _ _ _) body
            | isIgnoredBinding bnd -> Just body
        _ -> Nothing

extractIndexingInto :: (Binding -> Bool) -> Expression -> [(Int, Binding)]
extractIndexingInto f program =
    hashNub
        [ (fromIntegral n, st)
        | Nth n _ (expectVarE -> st) <- universe program
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
-- UPDATE: I think I may have fixed that actually
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

type UDFAccessedField = (Binding, Int)

baseUdfSubMap ::
       QualifiedBinding -> Binding -> [UDFAccessedField] -> Substitutions
baseUdfSubMap udfName rowName accessedFields =
    [ "udf-name" ~> [T.toTitle $ unwrap $ udfName ^. name]
    , "udf-name-str" ~> ["\"" <> unwrap (udfName ^. name) <> "\""]
    , "row-name" ~> [unwrap rowName]
    , "special-state-coerce-call" ~>
      ["." <> mkSpecialStateCoerceName udfName <> "()"]
    , "node-properties" ~>
      map (\e -> unwrap (idxPropFromName e) <> ": usize,") accessedFields
    , "node-property-args" ~>
      map ((<> ",") . unwrap . idxPropFromName) accessedFields
    , "udf-args" ~> ["udf_arg_placeholder,"]
    , "udf-args-sigs" ~> ["udf_arg_placeholder: usize,"]
    ]

generatedOpSourcePath :: QualifiedBinding -> FilePath
generatedOpSourcePath udfName =
    noriaDataflowSourceDir <> "/ops/ohua/generated/" <>
    toString (unwrap $ udfName ^. name) <>
    ".rs"

processStatefulUdf ::
       (MonadOhua m)
    => Fields
    -> QualifiedBinding
    -> Expression
    -> Binding
    -> Expression
    -> m (Expression, OperatorDescription)
processStatefulUdf fields udfName program state initState =
    case program of
        Let unit (Smap _ mapF (Var coll)) reduceF
            | isIgnoredBinding unit -> do
                (mapFn, rowName, fieldIndices) <- mkMapFn fields mapF state coll
                reduceFn <- mkReduceFn fields state reduceF
                let nodeSub =
                        TemplateSubstitution "map-reduce/op.rs" (generatedOpSourcePath udfName) $
                        baseUdfSubMap udfName rowName accessedFields <>
                        [ "map" ~> ["use " <> stateNSStr <> "::Action;", mapFn]
                        , "reduce" ~> [reduceFn]
                        , "special-state-coerce-call" ~>
                          ["." <> mkSpecialStateCoerceName udfName <> "()"]
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
                pure $ (ie,) $
                    Op_UDF $ UDFDescription
                        { generations = [nodeSub, stateSub]
                        , udfName = udfName
                        , inputBindings = []
                        , udfState = Just stateType
                        , referencedFields = fieldIndices
                        , execSemantic = ReductionSem
                        }
        _ -> error $ "Expected map-reduce pattern, got " <> quickRender program

-- HACK A dirty, dirty hack
getStateType initState =
    case [f | PureFunction f _ <- universe initState] of
        [f] -> f
        o -> error $ "Too many qualified applications in state init " <> show o

extractAcessedFields :: Expr -> [UDFAccessedField]
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
patchFiles :: (MonadIO m, MonadLogger m) => Maybe FilePath -> [UDFDescription] -> m ()
patchFiles mOutDir udfs =
    mapM_ (uncurry $ patchFile mOutDir) (HashMap.toList fileMap)
  where
    toMap =
        ([ noriaDataflowSourceDir <> "/ops/ohua/mod.rs" ~>
           ["link-generated-modules" ~> ["pub mod generated;"]]
         ] <>) .
        HashMap.fromListWith (HashMap.unionWith (<>))
    fileMap = toMap $ udfs >>= mkPatchesFor

mkPatchesFor :: UDFDescription -> [(FilePath, HashMap Text [Text])]
mkPatchesFor UDFDescription {..} =
      maybe []  (\st ->
        [noriaDataflowSourceDir <> "/state/mod.rs" ~>
          [ ("state-trait-method-def" :: Text) ~>
            mkStateTraitCoercionFunc udfName st "Option::None"
                -- fn as_click_ana_state<'a>(&'a mut self) -> Option<&'a mut self::click_ana::ClickAnaState> {
                --     Option::None
                -- }
          ] ]) udfState
        <>
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
    , noriaDataflowSourceDir <> "/ops/ohua/att3.rs" ~>
      [ let (replacementKey, extraNodeArg) =
                case execSemantic of
                    ReductionSem ->
                        ("generated-reducing-operator-inits", "group")
                    SimpleSem -> ("generated-simple-operator-inits", "carry")
         in replacementKey ~>
            [ renderDoc $ PP.dquotes (pretty udfName) <+> "=>" <+>
              ppBlock
                  (PP.vsep
                       [ "assert_eq!(over_cols.len(), " <>
                         pretty (1 `max` length referencedFields) <>
                         ");"
                       , pretty
                             (mkNodePath $ udfName & namespace . unwrapped .
                              ix 0 .~
                              "super") <>
                         "::new" <>
                         PP.tupled
                             ("parent" : "0" :
                              map
                                  (\n -> "over_cols" <> PP.brackets (pretty n))
                                  [0 .. pred $ length referencedFields] <>
                              [extraNodeArg])
                       ] <>
                   ".into()") <>
              ","
            ]
      ]
    , "noria-server/src/controller/schema.rs" ~>
      [ "type-resolution-for-generated-nodes" ~>
        [ renderDoc $ "ops::NodeOperator::" <> pretty nodeOpConstr <>
          PP.parens "ref n" <+>
          "=>" <+>
          "Some(n.typ()),"
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


rewriteQueryExpressions :: RegisterOperator -> Expr -> OhuaM env Expr
rewriteQueryExpressions register e = do
    logDebugN $ "Expression before Query EDSL rewrite: \n" <> quickRender e
    flip transformM e $ \case
        BindState st (Lit (FunRefLit (FunRef f _))) `Apply` arg
            | Just process <- queryEDSL f -> process register st [arg]
        other -> pure other

generateOperators :: Fields -> RegisterOperator -> Expression -> OhuaM env Expression
generateOperators fields registerOp program = do
    logInfoN $ "Complete expression for compilation\n" <> quickRender program
    program' <- transformM genStatefulOps program
        >>= transformM genPureOps
    logDebugN $ "Remaining program\n" <> quickRender program'
    pure program'
  where
    mempty' = mempty @(Dual (Endo Expr), HashSet.HashSet Binding)
    tellRet var = tell $ mempty' & _2 .~ HashSet.singleton var
    tellUdfE f = tell $ mempty' & _1 .~ Dual (Endo f)
    getDeps = map expectVarE . findFreeVariables
    go st (LetF v (oldExpr, expr) (extract -> body))
        | v == st =
            error $ "Invariant broken, state init happened in scope for " <>
            show st
        | otherwise = do
            body' <- body
                    -- Its a bit of a hack to record the return binding. It's
                    -- necessary because this pass is still a bit unstable in general.
            case body' of
                Var v -> _2 <>= [ v ]
                _ -> pure ()
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
        exprUsesState = or [s == Var st | BindState s _ <- universe oldExpr]
        eDeps = HashSet.fromList $ getDeps oldExpr
    go _ e'' = RS.embed <$> traverse extract e''
    genStatefulOps (Let st initExpr body)
        | st `HashSet.member` stateVals = do
            logDebugN $ "Considering the function:\n" <> quickRender body
            (e', _, (Dual (Endo mut), rets)) <-
                runRWST (RS.para (go st) body) () mempty
            bnd <- generateBindingWith ("op_s_" <> st)
            let udfName = QualifiedBinding GenFuncsNamespace bnd
                                 -- TODO This also necessitates changing the invoke expression to destructure this output!!
            logDebugN $ "Returns found " <> show rets
            (v', handleReturn) <- setupReturnRecieve $ HashSet.toList rets
            let udf = mut v'
                freeVars = filter (/= Var st) $ findFreeVariables udf
            logDebugN $ "Found operator function " <> quickRender udfName <>
                "\n" <>
                quickRender (Let st initExpr udf)
            ( invokeExpr, fdata ) <- processStatefulUdf fields udfName udf st initExpr
            liftIO $ registerOp fdata
            pure $ handleReturn invokeExpr e'
    genStatefulOps e = pure e
    genPureOps (Let bnd val@Apply {} body)
        | not $ isKnownFunction function = do
            opName <- generateBindingWith ("op_p_" <> function ^. name <> "_")
                        -- This relies heavily of having the expected `let x = f a b c`
                        -- structure
            let udfName = QualifiedBinding GenFuncsNamespace opName
                opGen =
                    TemplateSubstitution
                        "pure/op.rs"
                        (generatedOpSourcePath udfName) $
                    baseUdfSubMap udfName "r" accessedFields <>
                    [ "function" ~>
                      [ renderDoc $ asRust function <>
                        PP.tupled
                            (map (\i ->
                                      "r[self." <> pretty (idxPropFromName i) <>
                                      "].clone().into()")
                                 (if args == [Lit UnitLit]
                                      then []
                                      else accessedFields))
                      ]
                    , "udf-ret-type" ~> ["SqlType::Double"]
                    ]
            argVars <- traverse expectVar args
            liftIO $ registerOp $
                    Op_UDF $ UDFDescription
                        { udfName = udfName
                        , inputBindings = argVars
                        , udfState = Nothing
                        , referencedFields = fieldIndices
                        , generations = [opGen]
                        , execSemantic = SimpleSem
                        }
            pure $ Let bnd (fromListToApply (FunRef udfName Nothing) args) body
      where
        (FunRef function _, args) = fromApplyToList val
        fieldIndices = [0 .. length args - 1]
        accessedFields = map ("none", ) fieldIndices
    genPureOps other = pure other
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

isKnownFunction :: QualifiedBinding -> Bool
isKnownFunction f =
    f ^. namespace == GenFuncsNamespace || f ^? namespace . unwrapped . ix 0 ==
    Just "ohua"

setupReturnRecieve ::
       (Monad m, MonadGenBnd m) => [Binding] -> m (Expr, Expr -> Expr -> Expr)
setupReturnRecieve returns =
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
        TemplateSubstitution t (scopePath -> path) subs -> do
            p <- liftIO $ makeAbsolute path
            logDebugN $ "Outputting to path " <> fromString p
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

extraOperatorProcessing ::
       (MonadError Error m, MonadIO m, MonadLogger m) => Bool -> [OperatorDescription] -> m ()
extraOperatorProcessing useSandbox ops = do
    let udfs = mapMaybe (\case Op_UDF desc -> Just desc; _ -> Nothing) ops
    outDir <-
        if useSandbox
            then do
                fp <- liftIO $ createSysTempDir "noria-udfs"
                logInfoN
                    ("Writing files to sandbox directory " <> fromString fp)
                pure $ Just fp
            else pure Nothing
    let scopePath = maybe id (FP.</>) outDir
        mkPath d =
            scopePath $
            noriaDataflowSourceDir FP.</> d FP.</> "ohua/generated" FP.</>
            "mod.rs"
    doTheGenerating scopePath (udfs >>= generations)
    outputFile (mkPath "ops") $
        T.unlines $
        map (\u -> "pub mod " <> unwrap (udfName u ^. name) <> ";") udfs
    outputFile (mkPath "state") $
        T.unlines $
        mapMaybe
            (\case
                 u@(UDFDescription {udfState = Just _} ) ->
                     Just $ "pub mod " <> unwrap (udfName u ^. name) <> ";"
                 _ -> Nothing)
            udfs
    patchFiles outDir udfs
  where
    createSysTempDir pat =
        Temp.getCanonicalTemporaryDirectory >>= \sysd ->
            Temp.createTempDirectory sysd pat

mainArgsToTableRefs :: Expr -> (Word, [(Binding, Word)], Expr)
mainArgsToTableRefs = RS.para $ \case
    LambdaF a (_,  (i, l, e) ) -> (i + 1, (a,i):l, Let a (embedE ( QualifiedBinding [ "ohua", "sql", "rel" ] a ) `Apply` embedE UnitLit) e)
    other -> (0, [], RS.embed $ fmap fst other)
