{-# LANGUAGE TypeApplications, MultiWayIf, ConstraintKinds #-}

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
import Control.Monad.RWS (runRWST)
import Control.Monad.Writer (runWriterT, tell)
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

import Ohua.ALang.Lang
import Ohua.ALang.PPrint (ohuaDefaultLayoutOpts, quickRender)
import qualified Ohua.ALang.Passes as ALang (normalize)
import Ohua.ALang.Util (findFreeVariables, fromApplyToList, fromListToApply)
import qualified Ohua.CodeGen.NoriaUDF.Paths as Path
import Ohua.CodeGen.NoriaUDF.QueryEDSL (queryEDSL, rewriteFieldAccess)
import Ohua.CodeGen.NoriaUDF.Types
import Ohua.CodeGen.NoriaUDF.Util
import qualified Ohua.Frontend.Lang as Fr
import qualified Ohua.Frontend.NS as NS
import Ohua.Helpers.Template (Substitutions)
import Ohua.Standalone (CombinedAnn(..), PreResolveHook, RawNamespace)

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

makeStateReturn :: Expr -> Expr
makeStateReturn = transform $ \case
    Let unit val (Lit UnitLit) | isIgnoredBinding unit -> val
    e -> e

processStatefulUdf ::
       (MonadOhua m)
    => Fields
    -> QualifiedBinding
    -> Expression
    -> Binding
    -> Expression
    -> m (Expression, Either Expression OperatorDescription)
processStatefulUdf fields udfName program state initState = do
    logDebugN $ "Processing stateful UDF " <> quickRender program
    case program of
        Let unit stuff (Lit UnitLit)
            | isIgnoredBinding unit ->
              case length [v | Var v <- universe stuff, v == state] of
                  0 -> error "State not used. This should probably not be an error?"
                  n | n > 1 -> error $ "State " <> quickRender state <> " is used too often (" <> show n <> ")"
                  1 -> pure (makeStateReturn stuff, Left initState)
        Let unit (Smap _ mapF (Var coll)) reduceF
            | isIgnoredBinding unit -> do
                (mapFn, rowName, fieldIndices) <- mkMapFn fields mapF state coll
                reduceFn <- mkReduceFn fields state reduceF
                let nodeSub =
                        TemplateSubstitution
                            "map-reduce/op.rs"
                            (generatedOpSourcePath udfName) $
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
                pure $ (ie, ) $ Right $ Op_UDF $
                    UDFDescription
                        { generations = [nodeSub, stateSub]
                        , udfName = udfName
                        , inputBindings = []
                        , udfState = Just ( stateType, [] )
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


mkPatchesFor :: UDFDescription -> [(FilePath, HashMap Text [Text])]
mkPatchesFor UDFDescription {..} =
    maybe
        []
        (\( st, _ ) ->
             [ Path.dataflowSourceDir <> "/state/mod.rs" ~>
               [ ("state-trait-method-def" :: Text) ~>
                 mkStateTraitCoercionFunc udfName st "Option::None"
                -- fn as_click_ana_state<'a>(&'a mut self) -> Option<&'a mut self::click_ana::ClickAnaState> {
                --     Option::None
                -- }
               ]
             ])
        udfState <>
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
                                  (\n -> "over_cols" <> PP.brackets (pretty n) <> ".clone()")
                                  [0 .. pred $ length referencedFields] <>
                              [extraNodeArg])
                       ] <>
                   ".into()") <>
              ","
            ]
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

generateOperators ::
       Fields -> RegisterOperator -> Expression -> OhuaM env Expression
generateOperators fields registerOp program = do
    logInfoN $ "Complete expression for compilation\n" <> quickRender program
    logDebugN $ "Found state values" <> quickRender (HashSet.toList stateVals)
    program' <- evalStateT (transformM genStatefulOps program >>= transformM genPureOps) HashMap.empty
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
                Var v -> _2 <>= [v]
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
            (invokeExpr, fdata) <-
                processStatefulUdf fields udfName udf st initExpr
            case fdata of
                Left init -> modify (HashMap.insert st ( init, (Many, One) )) >> pure invokeExpr
                Right fdata -> do
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
            ( argVars, foldl (.) id -> extraLets ) <- unzip <$> traverse (\case Var v -> pure (v, id); other -> do b <- generateBindingWith "arg"; pure (b, Let b other) ) args
            (udfState, execSem) <- case st of
                 Nothing -> pure (Nothing, SimpleSem)
                 Just (Var v) ->
                     first (Just . stateToInit ) . fromMaybe (error $ "No initializer found for " <> quickRender v)
                     <$> gets (HashMap.lookup v)
                 Just other -> error $ "State should be a var " <> quickRender other
            liftIO $ registerOp $ Op_UDF $
                UDFDescription
                    { udfName = udfName
                    , inputBindings = argVars
                    , udfState = udfState
                    , referencedFields = fieldIndices
                    , generations = [opGen]
                    , execSemantic = execSem
                    }
            pure $ extraLets $ Let bnd (fromListToApply (FunRef udfName Nothing) (map Var argVars)) body
      where
        (st, FunRef function _, args) = stateAwareApplyToList val
        fieldIndices = [0 .. length args - 1]
        accessedFields = map ("none", ) fieldIndices
    genPureOps other = pure other
    stateVals =
        HashSet.fromList
            [ v
            | BindState st _ <- universe program
            , v <-
                  case st of
                      Var v -> [v]
                      e -> error (show e)
            ]

stateToInit :: Expr -> (QualifiedBinding, [Lit])
stateToInit e = (fun, [case l of Lit l -> l; _ -> error $ quickRender l <> " is not a literal" | l <- args])
  where (FunRef fun _, args) = fromApplyToList e

stateAwareApplyToList :: Expr -> (Maybe Expr, FunRef, [Expr])
stateAwareApplyToList = \case
    Apply f val -> let (s, f', e) = stateAwareApplyToList f in (s, f', e ++ [val])
    BindState v (Lit (FunRefLit f)) -> (Just v, f, [])
    Lit (FunRefLit f) -> (Nothing, f, [])
    e -> error $ quickRender e <> " is not a function application"

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
