{-# LANGUAGE TypeApplications #-}
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

import Ohua.Prelude hiding (First)

import Control.Monad.Writer (runWriterT, tell)
import qualified Data.Functor.Foldable as RS
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Text.Prettyprint.Doc ((<+>), pretty)
import qualified Data.Text.Prettyprint.Doc.Render.Text as PP
import System.Directory (createDirectoryIfMissing)
import qualified System.FilePath as FP
import qualified System.IO.Temp as Temp
import Control.Lens (ix, (<>=))
import qualified Data.Text as T
import Control.Arrow ((***))
import Control.Category ((>>>))
import Ohua.Standalone (PreResolveHook)
import Control.Monad.RWS (runRWST)
import Control.Comonad (extract)

import qualified Ohua.Frontend.NS as NS
import Ohua.ALang.Lang
import Ohua.ALang.PPrint (ohuaDefaultLayoutOpts, quickRender)
import Ohua.ALang.Util (findFreeVariables)
import Ohua.CodeGen.Iface
import qualified Ohua.CodeGen.JSONObject as JSONObject
import qualified Ohua.DFGraph as DFGraph
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
    , referencedFields :: [Binding]
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
    T.break (== ':')
    >>> (makeThrow . T.strip *** T.strip . T.drop 1)

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

idxPropFromName :: (Binding, Binding) -> Binding
idxPropFromName (st, f) = pwu st <> pwu f <> "index"
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
    -> m (Text, Binding)
mkMapFn fields program' stateV coll = do
    logInfoN $
        "Compiling udf-map function on state " <> unwrap stateV <>
        " and collection " <>
        unwrap coll <>
        "\n" <>
        quickRender program'
    freeVars <-
        filter (not . (`HashSet.member` predefVars)) <$>
        traverse expectVar (findFreeVariables program)
    unless (null freeVars) $
        throwError $
        "Expected not to find free variables, found " <> show freeVars <>
        " in\n" <>
        quickRender program
    inLoopFieldVars <- traverse (generateBindingWith . snd) loopAcessedFields
    let inLoop =
            PP.vsep $
            [ if exp == rowName
                then "let" <+>
                     pretty fieldVar <+>
                     ": &" <> pretty (resolveFieldType field) <+>
                     "= &" <> pretty rowName <> "[self." <>
                     pretty (idxPropFromName a) <>
                     "].clone().into();"
                else error $
                     "Access to fields from outside the row is not implemented yet (got: " <>
                     quickRender exp <>
                     ")\n" <>
                     quickRender program
            | (a@(exp, field), fieldVar) <-
                  zip loopAcessedFields inLoopFieldVars
            ] ++
            [toRust True program]
        resolveFieldVar v =
            fromMaybe (error $ "Field var not found for " <> show v) $
            HashMap.lookup
                v
                (HashMap.fromList $ zip loopAcessedFields inLoopFieldVars)
        resolveFieldType fi =
            fromMaybe (error $ "Use of undeclared field " <> unwrap fi) $
            HashMap.lookup fi fields
        function = "let _ = " <> ppBlock inLoop <> ";"
        toRust = Ohua.CodeGen.NoriaUDF.toRust resolveFieldVar isTheState mkAc
        mkAc func' args =
            "diffs.push" <> "((Action::" <> pretty (T.toTitle (unwrap func')) <>
            (if null args || args == [Lit UnitLit]
                 then mempty
                 else PP.tupled (map (toRust False) args)) <>
            ", r_is_positive))"
    pure (renderDoc function, rowName)
  where
    predefVars = HashSet.fromList [stateV, coll, rowName]
    isTheState = (== Var stateV)
    (program, rowName) =
        case program' of
            Lambda a b -> (b, a)
            _ ->
                error $
                "Expected lambda as input to smap, got " <> quickRender program'
    loopAcessedFields = extractAcessedFields program

refBelongsToState :: a -> Bool
refBelongsToState = const True

ppBlock :: PP.Doc ann -> PP.Doc ann
ppBlock e = PP.braces (PP.line <> PP.indent 4 e <> PP.line)

-- I am not sure about this one yet. Potentially the function being called on the state should always be fully qualified

toRust ::
       ((Binding, Binding) -> Binding)
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
            "else" <+> ppBlock (recurse True else_)
        e@(Apply _ _) ->
            case f of
                Var v -> mkFunctionCall (pretty v) args
                BindState st func -> handleBindState st func args
                Lit (FunRefLit (FunRef ref _)) ->
                    case ref ^. namespace of
                        OhuaFieldNS
                            | [h] <- args ->
                                pretty $
                                resolveFieldVar (expectVarE h, ref ^. name)
                            | otherwise ->
                                error $
                                "Expected only one argument for field access, got " <>
                                quickRender e
                        ["primitives"] ->
                            case ref ^. name of
                                "eq" -> binop "=="
                                "deref"
                                    | [expr] <- args ->
                                        "*" <> recurse False expr
                                    | otherwise -> wrongNumArgsErr "&" 1
                                "divide" -> binop "/"
                                other ->
                                    error $
                                    "Unknown primitive function " <>
                                    unwrap other
                            where wrongNumArgsErr func num =
                                      error $
                                      "Wrong number of arguments to " <> func <>
                                      " expected " <>
                                      show num <>
                                      " got " <>
                                      show (length args)
                                  binop op
                                      | [e1, e2] <- args =
                                          recurse False e1 <+>
                                          pretty op <+> recurse False e2
                                      | otherwise = wrongNumArgsErr op 2
                        _ -> mkFunctionCall (asRust ref) args
                _ -> error $ "Unexpected type of function expression " <> show f
            where (f, args) = disassembleCall e
        l@(Lambda _ _) -> error $ "Unexpected lambda " <> quickRender l
        Let b e1 body ->
            (if isInBlock
                 then id
                 else ppBlock) $
            (if isIgnoredBinding b
                 then id
                 else ("let" <+> pretty b <+> "=" <+>)) $
            recurse False e1 <> ";" <> PP.line <> recurse True body
        Lit l ->
            case l of
                NumericLit n -> pretty n
                UnitLit -> "()"
                FunRefLit (FunRef ref _) -> asRust ref
                _ -> error $ "Unexpected literal " <> show l
  where
    recurse = toRust resolveFieldVar isTheState mkAc
    disassembleCall =
        (second reverse .) $
        RS.para $ \case
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
                    error $
                    "Multiple states and renaming aren't supported yet " <>
                    show st
            _ -> error $ "Unexpected function expression " <> quickRender func
class ToRust t where
    asRust :: t -> PP.Doc ann

instance ToRust NSRef where
    asRust = PP.hcat . intersperse "::" . map (pretty . unwrap ) . unwrap

instance ToRust QualifiedBinding where
    asRust b = asRust (b ^. namespace) <> "::" <> pretty (unwrap $ b ^. name)

asRustT :: ToRust a => a -> Text
asRustT = renderDoc . asRust


isIgnoredBinding :: Binding -> Bool
isIgnoredBinding b = b == "()" || "_" `T.isPrefixOf` unwrap b

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
        error $
        "Field access not allowed in reduce right now. Attempted " <> show v
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
asNonEmpty f (x:xs) = f (x:|xs)

processUdf ::
       (MonadGenBnd m, MonadError Error m, MonadLogger m)
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
                (mapFn, rowName) <- mkMapFn fields mapF state coll
                reduceFn <- mkReduceFn fields state reduceF
                let nodeSub =
                        TemplateSubstitution
                            "map-reduce/op.rs"
                            (noriaDataflowSourceDir <> "/ops/ohua/generated/" <>
                             toString (unwrap $ udfName ^. name) <>
                             ".rs")
                            [ "udf-name" ~>
                              [T.toTitle $ unwrap $ udfName ^. name]
                            , "map" ~>
                              ["use " <> stateTypeStr <> "::Action;", mapFn]
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
                            ]
                    stateType = getStateType initState
                    stateTypeStr =
                        asRustT $ (getStateType initState ^. namespace) &
                        unwrapped @NSRef .
                        asNonEmpty %~
                        init &
                        unwrapped @NSRef .
                        ix 0 %~ \case
                            "dataflow" -> "crate"
                            i -> i
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
                logDebugN $ unlines $ "Acessed fields:" : map show accessedFields
                logInfoN $ "UDF " <> show udfName <> " callable with " <>
                    renderDoc
                        (pretty (udfName ^. name) <>
                         PP.tupled (map (pretty . snd) accessedFields))
                pure $
                    FData
                        { generations = [nodeSub, stateSub]
                        , udfName = udfName
                        , inputBindings = []
                        , udfState = stateType
                        , referencedFields = map idxPropFromName accessedFields
                        }
        _ -> error $ "Expected map-reduce pattern, got " <> quickRender program
  where
    accessedFields = extractAcessedFields program

-- HACK A dirty, dirty hack
getStateType initState =
    case [f | PureFunction f _ <- universe initState] of
        [f] -> f
        o -> error $ "Too many qualified applications in state init " <> show o

extractAcessedFields :: Expr -> [(Binding, Binding)]
extractAcessedFields program =
    hashNub
    [ (expectVarE st, fun ^. name)
    | PureFunction fun _ `Apply` st <- universe program
    , fun ^. namespace == OhuaFieldNS
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

generate :: CodeGen
generate = JSONObject.generate
    -- Assumes, for the time being, that state scope does not overlap

mkStateTraitCoercionFunc :: QualifiedBinding -> QualifiedBinding -> Text -> [ Text ]
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
mkNodePath udfName =
    udfFileToPathThing ModPath udfName [mkOpStructName udfName]

noriaDataflowSourceDir = "noria-server/dataflow/src"


-- TODO create the state impls in map-reduce/state.rs needs sub key "state-trait-coerce-impls"
patchFiles :: (MonadIO m, MonadLogger m) => Maybe FilePath -> [FData] -> m ()
patchFiles mOutDir udfs =
    for_ (HashMap.toList fileMap) $ \(file, subs) -> do
        tmpl <- TemplateHelper.parseTemplate <$> readFile file
        writeF file =<<
            TemplateHelper.sub
                TemplateHelper.Opts {preserveSpace = True}
                tmpl
                subs
  where
    writeF =
        flip (maybe writeFile) mOutDir $ \dir filename content ->
            liftIO $ outputFile (dir FP.</> filename) content
    toMap = HashMap.fromListWith (HashMap.unionWith (<>))
    fileMap =
        toMap $ flip concatMap udfs $ \FData {..} ->
            let opStructName = mkOpStructName udfName
                nodeOpConstr = T.toTitle $ opStructName <> "UDF"
                nodePath = mkNodePath udfName
             in [ noriaDataflowSourceDir <> "/ops/mod.rs" ~>
                  [ "node-operator-enum" ~>
                    [nodeOpConstr <> "(" <> nodePath <> "),"]
                  , "nodeop-from-impl-macro-call" ~>
                    [ "nodeop_from_impl!(NodeOperator::" <> nodeOpConstr <> ", " <>
                      nodePath <>
                      ");"
                    ]
               -- nodeop_from_impl!(NodeOperator::ClickAnaUDF, ohua::click_ana::ClickAna);
                  , "impl-ingredient-mut-macro" ~>
                    [ "NodeOperator::" <> nodeOpConstr <>
                      "(ref mut i) => i.$fn($($arg),*),"
                    ]
                -- NodeOperator::ClickAnaUDF(ref mut i) => i.$fn($($arg),*),
                  , "impl-ingredient-ref-macro" ~>
                    [ "NodeOperator::" <> nodeOpConstr <>
                      "(ref i) => i.$fn($($arg),*),"
                    ]
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
                    pure
                        (renderDoc $
                         PP.dquotes
                             (pretty $ T.toTitle $ unwrap $ udfName ^. name) <+>
                         "=>" <>
                         ppBlock
                             (PP.vsep
                                  [ "assert_eq!(over_cols.len(), " <>
                                    pretty (length referencedFields) <>
                                    ");"
                                  , pretty
                                        (mkNodePath $ udfName & namespace .
                                         unwrapped .
                                         ix 0 .~
                                         "super") <>
                                    "::new" <>
                                    PP.tupled
                                        ("parent" : "0" :
                                         map
                                             (\n ->
                                                  "over_cols" <>
                                                  PP.brackets (pretty n))
                                             [0 .. pred $ length referencedFields] <>
                                         ["group"])
                                  ] <>
                              ".into()") <>
                         ",")
                  ]
                , noriaDataflowSourceDir <> "/ops/ohua/mod.rs" ~>
                  ["link-generated-modules" ~> ["pub mod generated;"]]
                ] :: [(FilePath, HashMap Text [Text])]

pattern GenFuncsNamespace :: NSRef

pattern GenFuncsNamespace <- ["ohua", "generated"]
  where GenFuncsNamespace = ["ohua", "generated"]

type Fields = HashMap.HashMap Binding Text

generateNoriaUDFs :: Fields -> AddUDF -> Expression -> OhuaM env Expression
generateNoriaUDFs fields addUdf program = do
    logInfoN $ "Complete expression for compilation\n" <> quickRender program
    (program', udfs) <-
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
         in runWriterT $
            transformM
                (\case
                     Let st initExpr body
                         | st `HashSet.member` stateVals -> do
                             (e', _, (Dual (Endo mut), rets)) <-
                                 runRWST (RS.para (go st) body) () mempty
                             bnd <- generateBindingWith ("udf_" <> st)
                             let udfName =
                                     QualifiedBinding GenFuncsNamespace bnd
                                 v'
                                     | [i] <- rets = i
                                     | otherwise =
                                         error $
                                         "Too many returns from udf " <>
                                         show rets
                                 udf = mut $ Var v'
                                 freeVars =
                                     filter (/= Var st) $ findFreeVariables udf
                             logInfoN $
                                 "Found udf function " <> quickRender udfName <>
                                 "\n" <>
                                 quickRender (Let st initExpr udf)
                             tell [(bnd, udfName, udf, st, initExpr)]
                             expr' <- newFunctionCall udfName
                             pure $ Let v' (foldl Apply expr' freeVars) e'
                     e -> pure e)
                program
    logInfoN $ "Remaining program\n" <> quickRender program'
    for_ @[_] udfs $ \(_, udfName, e, st, initExpr) ->
        liftIO . addUdf =<< processUdf fields udfName e st initExpr
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

outputFile :: MonadIO m => FilePath -> Text -> m ()
outputFile path content =
    liftIO $ do
        createDirectoryIfMissing True (FP.takeDirectory path)
        writeFile path content

noriaUdfExtraProcessing ::
       (MonadError Error m, MonadIO m, MonadLogger m) => Bool -> [FData] -> m ()
noriaUdfExtraProcessing useSandbox udfs = do
    templates <-
        HashMap.fromList <$>
        sequence
            [ (t, ) <$> loadTemplate t
            | udf <- udfs
            , TemplateSubstitution t _ _ <- generations udf
            ]
    let getTemplate t =
            fromMaybe
                (error $ "Invariant broken, template not found " <> toText t) $
            HashMap.lookup t templates
    outDir <-
        if useSandbox
            then do
                fp <- liftIO $ createSysTempDir "noria-udfs"
                logInfoN
                    ("Writing files to sandbox directory " <> fromString fp)
                pure $ Just fp
            else pure Nothing
    let scopePath = maybe id (FP.</>) outDir
    for_ udfs $ \FData {..} ->
        for_ generations $ \case
            TemplateSubstitution t (scopePath -> path) subs ->
                outputFile path =<<
                TemplateHelper.sub
                    TemplateHelper.Opts {preserveSpace = True}
                    (getTemplate t)
                    subs
            GenerateFile (scopePath -> path) content ->
                liftIO $ writeFile path content
    for_ (["ops", "state"] :: [FilePath]) $ \d ->
        outputFile
            (scopePath $
             noriaDataflowSourceDir FP.</> d FP.</> "ohua/generated" FP.</>
             "mod.rs") $
        T.unlines $
        map (\u -> "pub mod " <> unwrap (udfName u ^. name) <> ";") udfs
    patchFiles outDir udfs
  where
    loadTemplate t =
        liftIO $ do
            path <- getDataFileName $ "templates/noria" FP.</> t
            TemplateHelper.parseTemplate <$> readFile path
    createSysTempDir pat =
        Temp.getCanonicalTemporaryDirectory >>= \sysd ->
            Temp.createTempDirectory sysd pat
