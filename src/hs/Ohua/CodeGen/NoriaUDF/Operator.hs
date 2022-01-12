{-# LANGUAGE TypeApplications, MultiWayIf, ConstraintKinds, ViewPatterns #-}

module Ohua.CodeGen.NoriaUDF.Operator
    ( generateOperators
    , OperatorDescription(..)
    , UDFDescription(..)
    , RegisterOperator
    , GenerationType(..)
    , udfFileToPathThing
    , PathType(..)
    , ToRust(..)
    , (~>)
    , renderDoc
    , ExecSem(..)
    , ExecSemantic
    , pattern SimpleSem
    , pattern ReductionSem
    , rewriteQueryExpressions
    , mainArgsToTableRefs
    , rewriteFieldAccess
    , preResolveHook
    , mkPatchesFor
    , isFieldAccessor
    , makeStateExplicit
    , extractStateInitializers
    ) where

import Ohua.Prelude hiding (First, Identity)

import Control.Arrow ((***))
import Control.Category ((>>>))
import Control.Comonad (extract)
import Control.Lens
    ( Simple
    , (%=)
    , (<>=)
    , (^..)
    , (^?!)
    , _3
    , _Just
    , at
    , cons
    , each
    , itraverse
    , ix
    , non
    , to
    , use
    )
import Control.Monad.RWS (runRWST, RWST, evalRWST)
import Control.Monad.Writer (runWriterT, tell, listen, censor, MonadWriter)
import qualified Control.Exception
import qualified Data.Functor.Foldable as RS
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.IntMap as IM
import qualified Data.Text as T
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Text.Prettyprint.Doc ((<+>), pretty)
import qualified Data.Text.Prettyprint.Doc.Render.Text as PP
import Data.Traversable (for)
import System.Directory (createDirectoryIfMissing)
import qualified System.FilePath as FP
import qualified Data.Set as Set

import Ohua.ALang.Lang
import qualified Ohua.ALang.Passes as ALang
import Ohua.ALang.PPrint (ohuaDefaultLayoutOpts, quickRender)
import qualified Ohua.ALang.Passes as ALang (normalize)
import Ohua.ALang.Util (findFreeVariables, fromApplyToList, fromListToApply, destructure, mkApply)
import Ohua.DFLang.Lang
import Ohua.DFLang.PPrint
import qualified Ohua.CodeGen.NoriaUDF.Paths as Path
import Ohua.CodeGen.NoriaUDF.QueryEDSL (queryEDSL, rewriteFieldAccess)
import Ohua.CodeGen.NoriaUDF.Types
import Ohua.CodeGen.NoriaUDF.Util
import qualified Ohua.Frontend.Lang as Fr
import qualified Ohua.Frontend.NS as NS
import Ohua.Helpers.Template (Substitutions)
import Ohua.Standalone (CombinedAnn(..), PreResolveHook, RawNamespace)
import Ohua.CodeGen.NoriaUDF.Util

data OpExc
    = IllegalExpressionInThisContext Expr
    | NoInitializerFound Binding
    | FoundDFEnvVar LetExpr Lit
    | StateProducingFunctionShouldOnlyHaveOneOutput LetExpr
    | InputToStateCannotBeLocal LetExpr Binding
    | StatCannotBeModifiedTwice LetExpr Binding
    | NonVarState Expr
    | StateReadBeforeWriting LetExpr Binding
    | NotAFunctionApplication Expr
    deriving (Show)

instance Exception OpExc

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
            "diffs.push((Action::" <> pretty (T.toTitle (unwrap func')) <>
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

asNonEmpty :: Traversal [a] [b] (NonEmpty a) [b]
asNonEmpty _ [] = pure []
asNonEmpty f (x:xs) = f (x :| xs)

type UDFAccessedField = (Binding, Int)

baseUdfSubMap ::
       QualifiedBinding -> Binding -> [UDFAccessedField] -> Substitutions
baseUdfSubMap udfName rowName accessedFields =
    [ "udf-name" ~> [T.toTitle $ unwrap $ udfName ^. name]
    , "udf-name-str" ~> ["\"" <> unwrap (udfName ^. name) <> "\""]
    , "udf-arg-strs" ~>
      map (\e -> "&self." <> unwrap (idxPropFromName e) <> ",") accessedFields
    , "row-name" ~> [unwrap rowName]
    , "special-state-coerce-call" ~>
      ["." <> mkSpecialStateCoerceName udfName <> "()"]
    , "node-properties" ~>
      map (\e -> unwrap (idxPropFromName e) <> ": Value,") accessedFields
    , "node-property-args" ~>
      map ((<> ",") . unwrap . idxPropFromName) accessedFields
    , "udf-args" ~> ["udf_arg_placeholder,"]
    , "udf-args-sigs" ~> ["udf_arg_placeholder: usize,"]
    ]

generatedOpSourcePath :: QualifiedBinding -> FilePath
generatedOpSourcePath udfName =
    Path.dataflowSourceDir <> "/ops/ohua/generated/" <>
    toString (unwrap $ udfName ^. name) <>
    ".rs"

extractStateInitializers :: (HasCallStack, MonadLogger m, MonadGenBnd m ) => (Binding -> Expr -> m ()) -> Expr -> m Expr
extractStateInitializers register e = flip runReaderT mempty $ flip RS.cata e $ \case
    LetF v bod rest | isState v -> do
                         bod' <- bod
                         lift $ register v bod'
                         local (HashMap.insert v bod')
                             rest
    -- BindStateF s r -> do
    --     s >>= \case
    --         Var v -> BindState <$> asks (HashMap.! v) <*>
    --             r
    --         other -> throwStack $ NonVarState other
    other -> RS.embed <$> sequence other
  where
    isState = flip HashSet.member $ HashSet.fromList [case s of Var v -> v; _ -> throwStack (NonVarState s) | BindState s _ <- universe e ]


makeStateExplicit :: forall m. (MonadOhua m, HasCallStack) => RegisterOperator -> (Binding -> Maybe Expr) -> Expr -> m Expr
makeStateExplicit registerOp getState = makeStateExplicitWith $ \func state args -> do
    case getState state of
        Just st -> do
            opName <- generateBindingWith ("op_p_" <> func ^. name <> "_")
            let udfName = QualifiedBinding GenFuncsNamespace opName
            argVars <- traverse expectVar args
            liftIO $ registerOp $ Op_UDF $ mkStatefulOpDesc (func ^.name) st udfName argVars
            pure $ Lit $ FunRefLit $ FunRef udfName Nothing
        Nothing -> pure $ Var state `BindState` Lit (FunRefLit (FunRef func Nothing))

makeStateExplicitWith :: forall m. (MonadOhua m, HasCallStack) => (QualifiedBinding -> Binding -> [Expr] -> m Expr) -> Expr -> m Expr
makeStateExplicitWith = \registerOp e0 -> do
    let e = transform ALang.reduceLetA e0 -- yikes
    logDebugN $ "Program before explicit state rewrite\n" <> quickRender e
    let assertIsUnused b = assertM $ or [b == v | Var v <- universe e]
    res <- fmap fst $ evalRWST (RS.cata (go assertIsUnused (\qb b a -> lift $ registerOp qb b a)) e) mempty []
    n <- (ALang.normalize res)
    logDebugN $ "Program after explicit state\n"  <> quickRender n
    pure res
  where
    go :: (MonadReader (HashMap Binding Binding) t, MonadWriter [Binding] t, MonadState (HashMap Binding Binding) t, HasCallStack, MonadOhua t) => (Binding -> t ()) -> (QualifiedBinding -> Binding -> [Expr] -> t Expr) -> RS.Base Expr (t Expr) -> t Expr
    go assertIsUnused registerOp eIn = case eIn of
        LetF b (newVal) (bod) -> do
            (new', newValChanges) <- censor (const mempty) $ listen newVal
            case tryStateAwareApplyToList new' of
                Right (st, FunRef  function _, args) -> do
                    (augment, transLet) <- if
                        | Just s <- st -> do
                              assertM $ null newValChanges
                              case s of
                                  Var v -> do
                                      func <- registerOp function v args
                                      newS <- generateBindingWith v
                                      assertIsUnused b
                                      pure (HashMap.insert v newS, Let newS $ mkApply func args)
                                  _ -> throwStack $ NonVarState s
                        | null newValChanges -> pure (id, Let b new')
                        | otherwise -> do
                            newVals <- traverse generateBindingWith newValChanges
                            newOut <- generateBindingWith "st_ret"
                            let changes = HashMap.fromList $ zip newValChanges newVals
                            pure $ ( HashMap.union changes
                                  , Let newOut (ReduceState `Apply` new') . destructure (Var newOut) (b : newVals))
                    modify augment
                    local augment $ do
                        bod' <- bod
                        s <- state (,mempty)
                        transLet <$>
                            if HashMap.null s
                            then pure bod'
                            else do
                                let (toRet, toPack) = unzip $ HashMap.toList s
                                tell toRet
                                pure $ fromListToApply (FunRef "ohua.lang/(,)" Nothing) ( bod': map Var toPack)
                _ -> tell newValChanges >> Let b new' <$> bod
        --BindStateF {} -> throwStack . IllegalExpressionInThisContext . RS.embed <$> sequence eIn
        VarF v -> Var <$> asks (fromMaybe v . HashMap.lookup v)
        _ -> RS.embed <$> sequence eIn

-- HACK A dirty, dirty hack
getStateType initState =
    case [f | PureFunction f _ <- universe initState] of
        [f] -> f
        o -> error $ "Too many qualified applications in state init " <> show o

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


mkPatchesFor :: UDFDescription -> [(FilePath, HashMap Text [Text])]
mkPatchesFor UDFDescription {..} =
    [ Path.dataflowSourceDir <> "/state/mod.rs" ~>
        [ ("state-trait-method-def" :: Text) ~>
          maybe
            []
            (\( st, _ ) ->
                 mkStateTraitCoercionFunc udfName st "Option::None"
                -- fn as_click_ana_state<'a>(&'a mut self) -> Option<&'a mut self::click_ana::ClickAnaState> {
                --     Option::None
                -- }
               )
            udfState
        ]
    ]
        <>
    [ Path.dfOpsFile ~>
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
    , Path.opsInterfaceFile ~>
    let mkInit extraNodeArg =
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
                                  (\n -> "over_cols" <> PP.brackets (pretty n) <> ".clone()")
                                  [0 .. pred $ length referencedFields] <>
                              [extraNodeArg])
                       ] <>
                   ".into()") <>
              ","
            ]
        (red, simpl) = case execSemantic of
                           ReductionSem -> (mkInit "group", [])
                           SimpleSem -> ([], mkInit "carry")
    in
    [ "generated-reducing-operator-inits" ~> red
    , "generated-simple-operator-inits" ~> simpl
    ]
    , Path.schemaFile ~>
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

toSQLType :: TyExpr SomeBinding -> Text
toSQLType (TyRef (Unqual b))
    | b == "i32" = "SqlType::Int(32)"
    | b == "i64" = "SqlType::Int(64)"
    | b == "bool" = "SqlType::Tinyint"
toSQLType t = trace ("WARNING: No SQL equivalent known for type " <> show t :: Text) "unreachable!(\"Cannot convert return type of this function. This function cannot be called as the last node in a query.\")"

preResolveHook ::
       (MonadIO m, MonadError Error m, MonadLogger m)
    => RegisterOperator
    -> RawNamespace
    -> m RawNamespace
preResolveHook registerOp r =
    runGenBndT mempty $ do
        logDebugN $ "Hook is running for " <> quickRender (r ^. name)
        (newDecls, toTransform) <- runWriterT $ itraverse finder (r ^. decls)
        forM_ toTransform $ \(source, oldName, udfName) -> do
            let function = QualifiedBinding (r ^. name) oldName
                Fr.LamE pats fbody = source ^. value
                args = map (\(Fr.VarP v) -> v) pats
            let fieldIndices = [0 .. length args - 1]
                accessedFields = map ("none", ) fieldIndices
                opGen =
                    TemplateSubstitution
                        "pure/op.rs"
                        (generatedOpSourcePath udfName) $
                    baseUdfSubMap udfName "r" accessedFields <>
                    [ "function" ~>
                      [ renderDoc $ pretty $
                        foldr'
                            (\(t, a, i) ->
                                 Fr.LetE (Fr.VarP a) $ Fr.VarE $ unsafeMake $
                                 renderDoc $
                                 maybe
                                     (<> ".into()")
                                     (\t' o ->
                                          "Into::<" <>
                                          pretty (Annotated False t') <>
                                          ">::into" <>
                                          PP.parens o)
                                     t $
                                 "match &self." <>
                                 pretty (idxPropFromName i) <>
                                 " { Value::Column(c) => r[*c].clone(), Value::Constant(c) => c.clone() }")
                            fbody $
                        reverse $
                        zip3
                            (maybe (repeat Nothing) (map Just . NS.argTypes) $
                             typeAnn $
                             source ^.
                             annotation)
                            args
                            accessedFields
                      ]
                    , "udf-ret-type" ~>
                      [ toSQLType $
                        fromMaybe
                            (error $ "type for " <> unwrap oldName <> " unknown")
                            (source ^? annotation . to typeAnn . _Just .
                             to NS.retType)
                      ]
                    ]
            lift $ liftIO $ registerOp $ Op_UDF $
                UDFDescription
                    { udfName = udfName
                    , inputBindings = args
                    , udfState = Nothing
                    , referencedFields = fieldIndices
                    , generations = [opGen]
                    , execSemantic = SimpleSem
                    }
        logDebugN $ "New declared functions " <>
            T.unlines
                (map (\(k, v) -> unwrap k <> " = " <> quickRender (v ^. value)) $
                 HashMap.toList newDecls)
        pure $ r & NS.sfImports %~
            cons (GenFuncsNamespace, toTransform & each %~ view (_3 . name)) &
            NS.decls .~
            newDecls
  where
    finder nam a
        | any (\case
                   Fr.LitE (FunRefLit (FunRef (QualifiedBinding ["ohua", "noria_integration"] "make_udf") _)) ->
                       True
                   _ -> False)
             (genericAnn ann) = do
            let newFnName =
                    unsafeMake $
                    T.intercalate "_" (map unwrap $ unwrap $ r ^. name) <>
                    "_" <>
                    unwrap nam
                newName = QualifiedBinding GenFuncsNamespace newFnName
            logDebugN $ "Found candidate " <> unwrap nam
            tell $ asList [(a, nam, newName)]
            pure $ a & annotation .~ ann {genericAnn = []} & value .~
                Fr.LitE (FunRefLit (FunRef newName Nothing))
        | otherwise = pure a
      where
        ann = a ^. annotation

asList :: [a] -> [a]
asList = id

rewriteQueryExpressions :: RegisterOperator -> Expr -> OhuaM env Expr
rewriteQueryExpressions register e = do
    logDebugN $ "Expression before Query EDSL rewrite: \n" <> quickRender e
    flip transformM e $ \case
        BindState st (Lit (FunRefLit (FunRef f _))) `Apply` arg
            | Just process <- queryEDSL f -> process register st [arg]
        other -> pure other

mkStatefulOpDesc :: Binding -> Expr -> QualifiedBinding -> [Binding] -> UDFDescription
mkStatefulOpDesc function initState udfName args =
    UDFDescription
        { generations = [nodeSub, stateSub]
        , udfName = udfName
        , inputBindings = []
        , udfState = Just $ stateToInit initState
        , referencedFields = fieldIndices
        , execSemantic = ReductionSem
        }
  where
    nodeSub =
        TemplateSubstitution
                "map-reduce/op.rs"
                (generatedOpSourcePath udfName) $
            baseUdfSubMap udfName rowName accessedFields <>
            [ "map" ~>
                ["use " <> stateNSStr <> "::Action;"
                , renderDoc $
                    PP.vsep $
                    [ "let arg_" <> pretty idx <+>
                    "= match &self." <>
                    pretty (idxPropFromName (stateV, idx)) <>
                    "{Value::Constant(c) => c.clone(), Value::Column(c) => " <>
                    pretty rowName <> "[*c].clone()}.into();"
                    | (idx, _) <- argsWithIndices
                    ] ++
                    ["diffs.push((Action::" <> pretty (T.toTitle $ unwrap ( function :: Binding)) <>
                        (if null args
                            then mempty
                            else PP.tupled (map (\i -> "arg_" <> pretty i) fieldIndices)) <>
                        ", r_is_positive));"
                    ]
                ]
            , "reduce" ~> ["computer.compute_new_value()"]
            , "special-state-coerce-call" ~>
            ["." <> mkSpecialStateCoerceName udfName <> "()"]
            , "udf-state-type" ~> [stateTypeStr]
            ]
    state = "state"
    stateV = state
    rowName = "r"
    argsWithIndices = zip [0..] $ drop 1 args
    fieldIndices = map fst argsWithIndices
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
            (Path.dataflowSourceDir <> "/state/ohua/generated/" <>
            toString (unwrap $ udfName ^. name) <>
            ".rs")
            [ "state-trait-coerce-impls" ~>
            mkStateTraitCoercionFunc
                udfName
                stateType
                "Option::Some(self)"
            , "udf-state-type" ~> [stateTypeStr]
            ]



stateToInit :: Expr -> (QualifiedBinding, [Lit])
stateToInit e = (fun, [case l of Lit l -> l; _ -> error $ quickRender l <> " is not a literal" | l <- args])
  where (FunRef fun _, args) = fromApplyToList e

isKnownFunction :: QualifiedBinding -> Bool
isKnownFunction f =
    f ^. namespace == GenFuncsNamespace || f ^? namespace . unwrapped . ix 0 ==
    Just "ohua"


isFieldAccessor :: QualifiedBinding -> Maybe Binding
isFieldAccessor op
    | OhuaFieldNS <- op ^. namespace = Just $ op ^.name
    | otherwise = Nothing


mainArgsToTableRefs :: Expr -> (Word, [(Binding, Word)], Expr)
mainArgsToTableRefs =
    RS.para $ \case
        LambdaF a (_, (i, l, e)) ->
            ( i + 1
            , (a, i) : l
            , Let a
                  (embedE (QualifiedBinding ["ohua", "sql", "rel"] a) `Apply`
                   embedE UnitLit)
                  e)
        other -> (0, [], RS.embed $ fmap fst other)

stateAwareApplyToList :: HasCallStack => Expr -> (Maybe Expr, FunRef, [Expr])
stateAwareApplyToList = either Control.Exception.throw id . tryStateAwareApplyToList

tryStateAwareApplyToList :: HasCallStack => Expr -> Either ErrorWithTrace (Maybe Expr, FunRef, [Expr])
tryStateAwareApplyToList = \case
    Apply f val -> tryStateAwareApplyToList f >>= \(s, f', e) -> pure (s, f', e ++ [val])
    BindState v (Lit (FunRefLit f)) -> pure (Just v, f, [])
    Lit (FunRefLit f) -> pure (Nothing, f, [])
    e -> Left $ ErrorWithTrace callStack $ NotAFunctionApplication e


generateOperators :: Fields -> RegisterOperator -> (Binding -> Maybe Expr) -> DFExpr -> OhuaM env DFExpr
generateOperators _ registerOp getStateInit DFExpr{ .. } = do
    newExprs <- evalStateT ( traverse doRewrite letExprs ) mempty
    let exp =  DFExpr { letExprs = newExprs >>= id
                      , returnVar
                      }
    logDebugN $ "DFLang after operator generation\n" <> quickRender exp
    pure exp
  where
    isState = isJust . getStateInit
    doRewrite e@LetExpr{..}
        | not (isKnownFunction function) = do
              opName <- generateBindingWith ("op_p_" <> function ^. name <> "_")
                    -- This relies heavily of having the expected `let x = f a b c`
                    -- structure
              let udfName = QualifiedBinding GenFuncsNamespace opName
                  argNum = length callArguments
                  fieldIndices = [0..pred argNum]
                  argVars = map (\(i, v) -> case v of DFVar v -> v; _ -> "arg" <> show i) $ zip [0..] callArguments
                  accessedFields = ("none", ) <$> fieldIndices
                  likePure =
                      UDFDescription
                      { udfName = udfName
                      , inputBindings = argVars
                      , udfState = Nothing
                      , referencedFields = fieldIndices
                      , generations = [opGen]
                      , execSemantic = SimpleSem
                      }
                    where
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
                                    accessedFields)
                            ]
                          , "udf-ret-type" ~> ["SqlType::Double"]
                          ]
              (mnewInp, mnewOutput, newOp) <- case stateArgument of
                  Just (DFEnvVar v) -> throwStack $ FoundDFEnvVar e v
                  Just (DFVar v) ->
                      gets (HashMap.lookup v . snd) >>= \case
                      Nothing -> do
                          bnd <- generateBindingWith v
                          modify $ second $ HashMap.insert v bnd
                          gets (HashMap.lookup v . fst) >>= \case
                              Nothing -> throwStack $ NoInitializerFound v
                              Just st -> do
                                  pure $ (Nothing, Just bnd, mkStatefulOpDesc (function ^. name) (exprFromDFExpr st) udfName argVars)
                      Just _ -> throwStack $ StatCannotBeModifiedTwice e v
                  Nothing ->
                      (, Nothing, likePure)
                      <$> case [ b |  DFVar b <- callArguments, isState b ] of
                              [] ->
                                  pure Nothing
                              _ ->
                                  Just <$>
                                  traverse
                                  (\case
                                          DFVar v | isState v ->
                                                    gets $ DFVar
                                                    . fromMaybe (throwStack $ StateReadBeforeWriting e v)
                                                    . HashMap.lookup v
                                                    . snd
                                          other -> pure other)
                                  callArguments
              liftIO $ registerOp $ Op_UDF newOp
              pure $ pure $ e { stateArgument = Nothing
                              , functionRef = functionRef { nodeRef = udfName }
                              , callArguments = fromMaybe callArguments mnewInp
                              , output = maybe output pure mnewOutput
                              }
        -- A bit hacky, but this is how I can drop the state from ctrl
        | otherwise = return $ pure e
      where
        function = nodeRef functionRef
        exprFromDFExpr e@LetExpr{..} =
            foldl Apply (Lit $ FunRefLit $ FunRef (nodeRef functionRef) Nothing) $
            map (\case DFVar v -> throwStack $ InputToStateCannotBeLocal e v; DFEnvVar l -> Lit l) callArguments
