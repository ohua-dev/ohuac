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
    ) where

import Control.Monad.Writer (runWriterT, tell)
import qualified Data.Functor.Foldable as RS
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.Text as T
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Text.Prettyprint.Doc ((<+>), pretty)
import qualified Data.Text.Prettyprint.Doc.Render.Text as PP
import System.Directory (createDirectoryIfMissing)
import qualified System.FilePath as FP
import System.IO.Temp

import Ohua.ALang.Lang
import Ohua.ALang.PPrint (ohuaDefaultLayoutOpts, quickRender)
import Ohua.ALang.Util (findFreeVariables, mkLambda)
import Ohua.CodeGen.Iface
import qualified Ohua.CodeGen.JSONObject as JSONObject
import qualified Ohua.DFGraph as DFGraph
import Ohua.Helpers.Template (Substitutions, Template)
import qualified Ohua.Helpers.Template as TemplateHelper
import Ohua.Prelude

import Paths_ohuac

data GenerationType =
    TemplateSubstitution Template
                         Substitutions

data FData = FData
    { generations :: [GenerationType]
    , udfName :: QualifiedBinding
    , inputBindings :: [Binding]
    }

type AddUDF = FData -> IO ()

-- | Just a simple helper to make writing the HashMap literals nicer
(~>) :: a -> b -> (a, b)
a ~> b = (a, b)

infixl 4 ~>

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
        ((PureFunction "ohua.lang/ifThenElse" _ `Apply` cond) `Apply`
           then_)
          `Apply` else_

idxPropFromName :: (Maybe Binding, Binding) -> Text
idxPropFromName (st, f) = maybe "" pwu st <> pwu f <> "index"
  where
    pwu (unwrap -> bnd) = bnd <> "__"

-- TODO generate node struct with indices for free vars
-- TODO make sure during SSA the bindings that the ambient code in noria is going to add are renamed if they occur here
-- NOTE Assume, for the time being, there is only one state
mkMapFn ::
       (MonadGenBnd m, Monad m, MonadError Error m)
    => Expression
    -> Binding
    -> Binding
    -> m (Text, Binding)
mkMapFn program' stateV coll = do
    freeVars <-
        filter (/= coll) <$> traverse expectVar (findFreeVariables program)
    unless (null freeVars) $
        throwError $
        "Expected not to find free variables, found " <> show freeVars
    inLoopFieldVars <- traverse (generateBindingWith . snd) loopAcessedFields
    let inLoop =
            PP.hsep $
            "use self::state::Action;" :
            map
                (\(a@(exp, field), fieldVar) ->
                     if exp == Just rowName
                         then "let" <+>
                              pretty fieldVar <+>
                              "= &" <> pretty rowName <> "[self." <>
                              pretty (idxPropFromName a) <>
                              "].clone().into();"
                         else error $
                              "Access to fields from outside the row is not implemented yet (got: " <>
                              quickRender exp <>
                              ")")
                (zip loopAcessedFields inLoopFieldVars) ++
            [toRust True program]
        resolveFieldVar v =
            fromMaybe (error $ "Field var not found for " <> show v) $
            HashMap.lookup
                v
                (HashMap.fromList $ zip loopAcessedFields inLoopFieldVars)
        function = inLoop
        loop =
            "for" <+> pretty rowName <+> "in" <+> pretty coll <+> ppBlock inLoop
        toRust = Ohua.CodeGen.NoriaUDF.toRust resolveFieldVar isTheState mkAc
        mkAc func' args =
            "diffs.push" <> "((Action::" <> pretty (T.toUpper (unwrap func')) <>
            (if null args
                 then mempty
                 else PP.tupled (map (toRust False) args)) <>
            ", r.is_positive()));"
    pure (renderDoc function, rowName)
  where
    isTheState = (== Var stateV)
    (program, rowName) =
        case program' of
            Lambda rowName program -> (program, rowName)
            _ ->
                error $
                "Expected lambda as input to smap, got " <> quickRender program'
    loopAcessedFields = extractAcessedFields program

refBelongsToState = const True

ppBlock e = PP.braces (PP.line <> PP.indent 4 e <> PP.line)

-- I am not sure about this one yet. Potentially the function being called on the state should always be fully qualified
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
                    pretty $
                    T.intercalate "::" $
                    map unwrap $ unwrap (ref ^. namespace) <> [ref ^. name]
                _ -> error $ "Unexpected type of function expression " <> show f
            where (f, args) = disassembleCall e
        Lambda _ _ -> error "Unexpected lambda"
        Let b e1 body ->
            (if isInBlock
                 then id
                 else ppBlock) $
            (if b == "()"
                 then id
                 else ("let" <+> pretty b <+> "=" <+>)) $
            recurse False e1 <> ";" <> PP.line <> recurse True body
        Lit l ->
            case l of
                NumericLit n -> pretty n
                UnitLit -> "()"
                _ -> error $ "Unexpected literal " <> show l
  where
    recurse = toRust resolveFieldVar isTheState mkAc
    disassembleCall =
        RS.para $ \case
            ApplyF (_, (f, args)) (arg, _) -> (f, arg : args)
            e -> (RS.embed $ fst <$> e, [])
    mkFunctionCall f args = f <> PP.tupled (map (recurse False) args)
    handleBindState st func =
        case func of
            Lit (FunRefLit (FunRef ref _))
                | ref ^. namespace == OhuaFieldNS ->
                    const $
                    pretty $ resolveFieldVar (Just $ expectVarE st, ref ^. name)
                | refBelongsToState (ref ^. namespace) && isTheState st ->
                    mkAc (ref ^. name)
            Var func'
                | isTheState st -> mkAc func'
                | otherwise ->
                    error $
                    "Multiple states and renaming aren't supported yet " <>
                    show st
            _ -> error $ "Unexpected function expression " <> quickRender func

renderDoc = PP.renderStrict . PP.layoutSmart ohuaDefaultLayoutOpts

mkReduceFn :: Applicative f => Binding -> Expression -> f Text
mkReduceFn state = pure . renderDoc . toRust True
  where
    toRust = Ohua.CodeGen.NoriaUDF.toRust resolveFieldVar isTheState mkAc
    isTheState = (== Var state)
    resolveFieldVar :: Show a => a -> Binding
    resolveFieldVar v =
        error $
        "Field access not allowed in reduce right now. Attempted " <> show v
    mkAc func' args =
        pretty (unwrap func') <> PP.tupled (map (toRust False) args) <> ";"

newFunctionCall :: (MonadGenId m, Functor m) => QualifiedBinding -> m Expression
newFunctionCall n = PureFunction n . Just <$> generateId

processUdf ::
       (MonadGenBnd m, Monad m, MonadError Error m)
    => Binding
    -> Expression
    -> m [GenerationType]
processUdf udfName program =
    case program of
        Let state initState (Let unit (Smap _ mapF (Var coll)) reduceF)
            | unit == "()" -> do
                (mapFn, rowName) <- mkMapFn mapF state coll
                reduceFn <- mkReduceFn state reduceF
                let nodeSub =
                        TemplateSubstitution
                            "map-reduce/op.rs"
                            [ "udf-name" ~> unwrap udfName
                            , "map" ~> mapFn
                            , "reduce" ~> reduceFn
                            , "row-name" ~> unwrap rowName
                            , "make-special-state" ~>
                              renderDoc
                                  (toRust
                                       (\v ->
                                            error $
                                            "Resolving fields not possible in state init yet. Got: " <>
                                            show v :: Binding)
                                       (const False)
                                       (error $
                                        "Cannot use state interactions here.")
                                       False
                                       initState)
                            , "sql-type" ~> "SqlType::Double" -- Do not hardcode this
                            , "node-properties" ~>
                              unlines
                                  (map (\e -> idxPropFromName e <> ": usize,")
                                       accessedFields)
                            ]
                    stateSub = TemplateSubstitution "map-reduce/state.rs" []
                pure [nodeSub, stateSub]
        _ -> error $ "Expected map-reduce pattern, got " <> show program
  where
    accessedFields = extractAcessedFields program

extractAcessedFields :: Expr -> [(Maybe Binding, Binding)]
extractAcessedFields program =
    [ (st, fun ^. name)
    | e <- universe program
    , (st, fun) <-
          case e of
              StatefulFunction fun _ st ->
                  pure
                      ( case st of
                            Var b -> Just b
                            _ ->
                                error $
                                "Field accessor can only be applied to var (for now), got " <>
                                quickRender st
                      , fun)
              PureFunction fun _ -> pure (Nothing, fun)
              _ -> []
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

-- TODO create the state impls in map-reduce/state.rs needs sub key "state-trait-coerce-impls"
patchFiles :: Maybe FilePath -> [FData] -> IO ()
patchFiles mOutDir udfs =
    for_ (HashMap.toList fileMap) $ \(file, subs) -> do
        tmpl <- TemplateHelper.parseTemplate <$> readFile file
        writeFile file $ TemplateHelper.sub tmpl $ fmap unlines subs
  where
    writeF =
        maybe writeFile $ \dir filename content -> do
            let name = dir FP.</> filename
            createDirectoryIfMissing True name
            writeFile name content
    toMap =
        HashMap.fromListWith (HashMap.unionWith (<>)) .
        fmap (second $ fmap pure)
    fileMap =
        toMap $
        flip concatMap udfs $ \FData {..} ->
            let opStructName = T.toUpper (unwrap $ udfName ^. name)
                nodeOpConstr = opStructName <> "UDF"
                nodePath =
                    udfFileToPathThing ModPath udfName ["op", opStructName]
             in [ "noria-server/dataflow/src/ops/mod.rs" ~>
                  [ "node-operator-enum" ~>
                    nodeOpConstr <> "(" <> nodePath <> "),"
                  , "nodeop-from-impl-macro-call" ~>
                    "nodeop_from_impl!(NodeOperator::" <> opStructName <> ", " <>
                    nodePath <>
                    ");"
               -- nodeop_from_impl!(NodeOperator::ClickAnaUDF, ohua::click_ana::ClickAna);
                  , "impl-ingredient-mut-macro" ~>
                    "NodeOperator::" <> nodeOpConstr <>
                    "(ref mut i) => i.$fn($($arg),*),"
                -- NodeOperator::ClickAnaUDF(ref mut i) => i.$fn($($arg),*),
                  , "impl-ingredient-ref-macro" ~>
                    "NodeOperator::" <> nodeOpConstr <>
                    "(ref i) => i.$fn($($arg),*),"
             -- NodeOperator::ClickAnaUDF(ref i) => i.$fn($($arg),*),
                  ]
                , "noria-server/dataflow/src/state/mod.rs" ~>
                  [ ("state-trait-method-def" :: Text) ~>
                    "fn as_" <> unwrap (udfName ^. name) <>
                    "_state<'a>(&'a mut self) -> Option<&'a mut " <>
                    nodePath <>
                    ("> {Option::None}" :: Text)
            -- fn as_click_ana_state<'a>(&'a mut self) -> Option<&'a mut self::click_ana::ClickAnaState> {
            --     Option::None
            -- }
                  ]
                ] :: [(FilePath, HashMap Text Text)]

generateNoriaUDFs :: AddUDF -> Expression -> OhuaM env Expression
generateNoriaUDFs addUdf program = do
    (program', udfs) <-
        let f =
                sequence >=> \case
                    e@(LetF v _ _)
                        | v `HashSet.member` stateVals -> do
                            fname <- generateBindingWith "udf"
                            let name =
                                    QualifiedBinding
                                        (makeThrow
                                             ["ohua", "noria", "generated"])
                                        fname
                            freeVars <-
                                traverse expectVar $
                                findFreeVariables $ RS.embed e
                            tell $ (RS.embed e, fname, name, freeVars) : []
                            --mkLambda freeVars <$>
                            newFunctionCall name
                    e -> pure $ RS.embed e
         in runWriterT $ RS.cata f program
    for_ udfs $ \(e, fname, name, freeVars) -> do
        code <- processUdf fname e
        liftIO $
            addUdf
                FData
                    { generations = code
                    , udfName = name
                    , inputBindings = freeVars
                    }
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

noriaUdfExtraProcessing ::
       (MonadError Error m, MonadIO m, MonadMask m) => Bool -> [FData] -> m ()
noriaUdfExtraProcessing useSandbox udfs = do
    templates <- loadTemplates udfs
    (\comp ->
         if useSandbox
             then withSystemTempDirectory
                      "noria-udfs"
                      (\fp ->
                           putStrLn
                               ("Writing files to sandbox directory " <> fp) >>
                           comp (Just fp))
             else comp Nothing) $ \outDir -> do
        for_ udfs $ \FData {..} -> do
            let genDir =
                    maybe id (FP.</>) outDir $
                    toString $ udfFileToPathThing FilePath udfName []
            liftIO $ createDirectoryIfMissing True genDir
            for_ generations $ \case
                TemplateSubstitution t subs
                    | Just tmpl <- HashMap.lookup t templates ->
                        liftIO $
                        writeFile (genDir FP.</> FP.takeFileName t) $
                        TemplateHelper.sub tmpl subs
                    | otherwise ->
                        throwError $
                        "Invariant broken, template not found " <> toText t
        liftIO $ patchFiles outDir udfs
  where
    loadTemplates =
        fmap HashMap.fromList .
        traverse (\t -> (t, ) <$> loadTemplate t) .
        concatMap
            (\(generations -> g) ->
                 flip map g $ \case
                     TemplateSubstitution t _ -> t)
    loadTemplate t =
        liftIO $ do
            path <- getDataFileName t
            TemplateHelper.parseTemplate <$> readFile path
