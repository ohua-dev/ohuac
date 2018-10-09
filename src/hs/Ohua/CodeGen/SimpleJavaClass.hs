{-# LANGUAGE NoOverloadedLists #-}
module Ohua.CodeGen.SimpleJavaClass (generate) where

import Ohua.Prelude

import Text.Casing
import qualified Data.Text as T
import qualified Data.HashMap.Strict as HM
import Data.List (nub)
import Data.Version
import Language.Java.Syntax as Java
import Language.Java.Pretty (prettyPrint)
import qualified Data.ByteString.Lazy.Char8 as LB

import Ohua.DFGraph
import Ohua.ALang.NS
import Ohua.CodeGen.Iface

import Paths_ohuac

-- A hack for now, this should be shared later
tupleConstructor :: TyExpr SomeBinding
tupleConstructor = TyRef $ Qual $ QualifiedBinding (unsafeMake []) "(,)"


generationInfoString :: LByteString
generationInfoString = "Generated with ohuac, version " <> LB.pack (showVersion version)


stringifyQual :: QualifiedBinding -> String
stringifyQual QualifiedBinding {..} =
    toString $
    T.intercalate "." (map unwrap $ unwrap qbNamespace) <> "/" <> unwrap qbName

-- | Caveat: This function does not support all java types yet. Notably the
-- primitive types and wildcard generics are missing
tyExprToJava :: TyExpr SomeBinding -> Java.Type
tyExprToJava = RefType . go []
  where
    formatRef sb l =
        ClassRefType $
        ClassType $
        case sb of
            Unqual b -> mkLast b
            Qual (QualifiedBinding ns bnd) ->
                map ((, []) . Ident . toString . unwrap) (unwrap ns) ++
                mkLast bnd
      where
        mkLast b = [(Ident $ toString $ unwrap b, map ActualType l)]
    go l = \case
      TyRef ref -> formatRef ref l
      TyApp t1 t2 -> go (go [] t2 : l) t1

isVoidType :: TyExpr SomeBinding -> Bool
isVoidType = (== tupleConstructor)


-- Identities
returnVarI, lazyI, arcIdent, graphIdent, objectI, arcI, graphClassI
  , codeGenHelperClassI, opsFieldName, arcsFieldName, configuredClassI
  , runtimeConfigurationFieldI, preparedClassI, cloneMethodI
  , runnableAlgoFieldI, configVarIdent, prepareMethodI, invokeMethodI
  , configureMethodI :: Ident
returnVarI = Ident "returnVar"
lazyI = Ident "Lazy"
arcIdent = Ident "Arc"
graphIdent = Ident "graph"
objectI = Ident "Object"
arcI = Ident "Arc"
graphClassI = Ident "Graph"
codeGenHelperClassI = Ident "CodeGenHelper"
opsFieldName = Ident "ops"
arcsFieldName = Ident "arcs"
configuredClassI = Ident "Configured"
runtimeConfigurationFieldI = Ident "runtimeConfiguration"
preparedClassI = Ident "Prepared"
cloneMethodI = Ident "clone"
runnableAlgoFieldI = Ident "runnableAlgo"
configVarIdent = Ident "configuration"
prepareMethodI = Ident "prepare"
invokeMethodI = Ident "invoke"
configureMethodI = Ident "configure"

runtimeConfigurationFieldVarId :: VarDeclId
runtimeConfigurationFieldVarId = VarId runtimeConfigurationFieldI

-- Class types
operatorClassRef, nonGenericArcClassRef, sfRefHelperClass
  , configurationClassType :: ClassType
operatorClassRef = ClassType [(Ident "Operator", [])]
sfRefHelperClass =
        ClassType [(codeGenHelperClassI, []), (Ident "SfRef", [])]
configurationClassType = ClassType [(Ident "RuntimeProcessConfiguration", [])]

objectType, configurationType, graphType, runnableAlgoType :: Java.Type
objectType = RefType objectRefType
configurationType = RefType $ ClassRefType configurationClassType
graphType =
    RefType $
    ClassRefType $ ClassType [(graphClassI, [ActualType lazyObjectRefT])]
runnableAlgoType = RefType $ ClassRefType $ ClassType [(Ident "Runnable", [])]

objectRefType, lazyObjectRefT :: RefType
objectRefType = ClassRefType $ ClassType [(objectI, [])]
lazyObjectRefT =
    ClassRefType $
    ClassType
        [(lazyI, [ActualType $ ClassRefType $ ClassType [(objectI, [])]])]
nonGenericArcClassRef = ClassType [(arcI, [])]

indexToArgument, indexToArgumentLazy :: Int -> Ident
indexToArgument = Ident . mappend "argument" . show
indexToArgumentLazy = Ident . mappend "lazyArgument" . show

simpleImport :: [String] -> ImportDecl
simpleImport path = ImportDecl False (Name $ map Ident path) False

envSourceTypeDeclSpec :: TypeDeclSpecifier
envSourceTypeDeclSpec =
    TypeDeclSpecifierWithDiamond
        (ClassType [(Ident "Source", [])])
        (Ident "Env")
        Diamond

-- | @assignArcArray idx exp@ creates a
-- @
--    arcs[idx] = exp;
-- @
-- statement
assignArcArray :: Int -> Exp -> Stmt
assignArcArray idx =
    ExpStmt .
    Assign
        (ArrayLhs $
          ArrayIndex
              (ExpName (Name [arcsFieldName]))
              [Lit $ Int $ toInteger idx])
        EqualA

-- `new` expressions

-- | Create a @new Target(opId, index)@ from a 'Target' record
newTarget :: Target -> Exp
newTarget Target {..} =
    InstanceCreation
        []
        (TypeDeclSpecifier $ ClassType [(Ident "Target", [])])
        [ Lit $ Int $ toInteger $ unwrap operator
        , Lit $ Int $ toInteger index
        ]
        Nothing

-- | Creates a @new Source.Local(target)@ or @new Source.Env(lazyObject)@ from
-- an 'Arc'
newSource :: Source HostExpr -> Exp
newSource (LocalSource target) =
    InstanceCreation
        []
        (TypeDeclSpecifier $
          ClassType [(Ident "Source", []), (Ident "Local", [])])
        [newTarget target]
        Nothing
newSource (EnvSource idx) =
    InstanceCreation
        []
        envSourceTypeDeclSpec
        [ExpName $ Name $ pure $ indexToArgumentLazy $ unwrap idx]
        Nothing

-- | Creates an @new Operator(opId, opType)@ expression from an 'Operator' record.
newOp :: Operator -> Exp
newOp Operator {..} =
    InstanceCreation
        []
        (TypeDeclSpecifier operatorClassRef)
        [ Lit $ Int $ toInteger $ unwrap operatorId
        , Lit $ String $ stringifyQual operatorType
        ]
        Nothing

-- | Creates an @new Arc<>(target, source)@ expression from an 'Arc'
newArc :: Arc HostExpr -> Exp
newArc Arc {..} =
    InstanceCreation
        []
        (TypeDeclSpecifierUnqualifiedWithDiamond arcIdent Diamond)
        [newTarget target, newSource source]
        Nothing

-- | Creates an @Lazy.createRealized(argument)@ expression given the input
-- argument to the method
createRealizedLazyExp :: Argument -> Exp
createRealizedLazyExp val =
    MethodInv $
    TypeMethodCall (Name [lazyI]) [] (Ident "createRealized") [val]

mkCommonArrayField :: ClassType -> Ident -> Maybe VarInit -> MemberDecl
mkCommonArrayField classRef fieldName initExprs =
    FieldDecl
        [Private, Static, Final]
        (RefType $ ArrayType $ RefType $ ClassRefType classRef)
        [VarDecl (VarId fieldName) initExprs]

configuredClassDecl :: Ident -> [Java.Type] -> ClassDecl
configuredClassDecl mainClassName invokeMethodTypes =
    ClassDecl [Public, Final, Static] configuredClassI [] Nothing [] $
    ClassBody
        [ MemberDecl runtimeConfigurationFieldDecl
        , MemberDecl configuredClassConstructorDecl
        , MemberDecl prepareMethodDecl
        ]
  where
    invokeMethodParamNames =
        [indexToArgument i | i <- [0 .. length invokeMethodTypes - 1]]
    invokeMethodParams =
        map (\(t, i) -> FormalParam [Final] t False (VarId i)) $
        zip invokeMethodTypes invokeMethodParamNames
    preparedClassType :: ClassType
    preparedClassType =
        ClassType $ map (, []) [mainClassName, preparedClassI]
    prepareMethodDecl :: MemberDecl
    prepareMethodDecl =
        MethodDecl
            [Final, Public]
            []
            (Just $ RefType $ ClassRefType preparedClassType)
            prepareMethodI
            invokeMethodParams
            []
            Nothing $
        MethodBody $
        Just $
        Block
            [ BlockStmt $
              Return $
              Just $
              InstanceCreation
                  []
                  (TypeDeclSpecifier preparedClassType)
                  (FieldAccess
                       (PrimaryFieldAccess This runtimeConfigurationFieldI) :
                   map (ExpName . Name . pure) invokeMethodParamNames)
                  Nothing
            ]

runtimeConfigurationFieldDecl :: MemberDecl
runtimeConfigurationFieldDecl =
    FieldDecl
        [Private, Final]
        configurationType
        [VarDecl runtimeConfigurationFieldVarId Nothing]

configuredClassConstructorDecl :: MemberDecl
configuredClassConstructorDecl =
    ConstructorDecl
        [Private]
        []
        configuredClassI
        [ FormalParam
              [Final]
              configurationType
              False
              runtimeConfigurationFieldVarId
        ]
        [] $
    ConstructorBody
        Nothing
        [ BlockStmt $
          ExpStmt $
          Assign
              (FieldLhs $ PrimaryFieldAccess This runtimeConfigurationFieldI)
              EqualA
              (ExpName $ Name [runtimeConfigurationFieldI])
        ]


generate :: CodeGen
generate CodeGenData {..} =
    pure
        ( T.intercalate "/" (map toText $ nsList ++ [classNameStr]) <> ".java"
        , LB.pack (prettyPrint classCode) <> "\n//" <> generationInfoString <> "\n")
    -- Values computed from CodeGenData
  where
    nsList = map (toSnake . fromAny . toString . unwrap) $ unwrap entryPointNamespace
    classNameStr = toPascal $ fromAny $ toString $ unwrap entryPointName
    className = Ident classNameStr
    retId = succ $ maximum $ map operatorId $ operators graph
    enumerateArgs = map unsafeMake [0 .. entryPointArity - 1]
    entryPointAnnotations = annotations >>= HM.lookup entryPointName
    returnType =
        case entryPointAnnotations of
            Nothing -> Just objectType
            Just (retType -> ann)
                | isVoidType ann -> Nothing
                | otherwise -> Just $ tyExprToJava ann
    argumentAnnotations :: [Java.Type]
    argumentAnnotations =
        maybe
            (replicate entryPointArity objectType)
            (map tyExprToJava . argTypes)
            entryPointAnnotations
    localArcs = [a | a@Arc {source = LocalSource _} <- arcs graph]
    envArcs = [a | a@Arc {source = EnvSource _} <- arcs graph]
    envArcCount = length envArcs
    isVoidFunction = isNothing returnType
    mainClassName = Name $ map Ident nsList <> [className]
    returnValueArc =
        newArc $
        Arc (Target retId 0) (LocalSource $ returnArc graph :: Source HostExpr)
    finalOperators
        | isVoidFunction = operators graph
        | otherwise = Operator retId "ohua.lang/capture" : operators graph
    addReturnCaptureArcs
        | isVoidFunction = identity
        | otherwise = (Lit Null :) . (returnValueArc :)
    invokeMethodArgNames = map (indexToArgument . unwrap) enumerateArgs
    invokeParams =
        [ FormalParam [] ty False (VarId vname)
        | (ty, vname) <- zip argumentAnnotations invokeMethodArgNames
        ]
    preparedClassDecl :: ClassDecl
    preparedClassDecl =
        ClassDecl [Public, Final, Static] preparedClassI [] Nothing [] $
        ClassBody $
        concat
            [ pure $ MemberDecl runnableFieldDecl
            , returnArcDecl
            , pure $ MemberDecl constructorDecl
            , pure $ MemberDecl invokeFunctionDecl
            ]
      where
        returnArcDecl = do
            let aRefId = Ident "AtomicReference"
            guard (not isVoidFunction)
            pure $
                MemberDecl $
                FieldDecl
                    [Final, Private]
                    (RefType $
                     ClassRefType $
                     ClassType [(aRefId, [ActualType objectRefType])])
                    [ VarDecl (VarId returnVarI) $
                      Just $
                      InitExp $
                      InstanceCreation
                          []
                          (TypeDeclSpecifierUnqualifiedWithDiamond
                               aRefId
                               Diamond)
                          []
                          Nothing
                    ]
        assignToField fieldName =
            BlockStmt .
            ExpStmt .
            Assign (FieldLhs $ PrimaryFieldAccess This fieldName) EqualA
        cloneArr fieldName =
            MethodInv $
            PrimaryMethodCall
                (FieldAccess $
                 PrimaryFieldAccess (ExpName mainClassName) fieldName)
                []
                cloneMethodI
                []
        runnableFieldDecl =
            FieldDecl
                [Private, Final]
                runnableAlgoType
                [VarDecl (VarId runnableAlgoFieldI) Nothing]
        constructorDecl =
            ConstructorDecl
                [Private]
                []
                preparedClassI
                (FormalParam
                     [Final]
                     configurationType
                     False
                     (VarId configVarIdent) :
                 invokeParams)
                [] $
            ConstructorBody Nothing constructorCode
        constructorCode =
            concat
                [ [ mkLocalArrVar operatorClassRef opsFieldName
                  , mkLocalArrVar nonGenericArcClassRef arcsFieldName
                  ]
                , createArgumentLazies
                , createAndAssignInputArcs
                , createAndAssignReturnArc
                , createLocalGraph
                , createAndAssignRunnableAlgo
                ]
          where
            mkLocalArrVar t fieldName =
                LocalVars
                    [Final]
                    (RefType $ ArrayType $ RefType $ ClassRefType t)
                    [ VarDecl
                          (VarId fieldName)
                          (Just $ InitExp $ cloneArr fieldName)
                    ]
            createArgumentLazies =
                [ LocalVars
                      [Final]
                      (RefType lazyObjectRefT)
                      [ VarDecl (VarId $ indexToArgumentLazy $ unwrap idx) $
                      Just $
                      InitExp $
                      createRealizedLazyExp
                          (ExpName $ Name $ pure $ indexToArgument $ unwrap idx)
                      | idx <- enumerateArgs :: [HostExpr]
                      ]
                ]
            createAndAssignInputArcs =
                [ BlockStmt $ assignArcArray arcIdx (newArc arc)
                | (arcIdx, arc) <- zip [(0 :: Int) ..] envArcs
                ]
            createAndAssignReturnArc = do
                guard (not isVoidFunction)
                pure $
                    BlockStmt $
                    assignArcArray envArcCount $
                    InstanceCreation
                        []
                        (TypeDeclSpecifierUnqualifiedWithDiamond
                             arcIdent
                             Diamond)
                        [ newTarget $ Target retId 1
                        , InstanceCreation
                              []
                              envSourceTypeDeclSpec
                              [ createRealizedLazyExp $
                                FieldAccess $ PrimaryFieldAccess This returnVarI
                              ]
                              Nothing
                        ]
                        Nothing
            createAndAssignRunnableAlgo =
                pure $
                assignToField runnableAlgoFieldI $
                MethodInv $
                TypeMethodCall
                    (Name [Ident "Runtime"])
                    []
                    (Ident "prepare")
                    [ ExpName $ Name [graphIdent]
                    , ExpName $ Name [configVarIdent]
                    ]
        invokeFunctionDecl =
            MethodDecl [Public, Final] [] returnType (Ident "invoke") [] [] Nothing $
            MethodBody $ Just invokeFunctionCode
        invokeFunctionCode =
            Block $
            concat
                [ pure $
                  BlockStmt $
                  ExpStmt $
                  MethodInv $
                  PrimaryMethodCall
                      (FieldAccess $ PrimaryFieldAccess This runnableAlgoFieldI)
                      []
                      (Ident "run")
                      []
                , invokeMethodReturnStatement returnType
                ]
    classCode =
        CompilationUnit
            packageDecl
            [ simpleImport ["ohua", "graph", "Arc"]
            , simpleImport ["ohua", "graph", "Operator"]
            , simpleImport ["ohua", "graph", "Target"]
            , simpleImport ["ohua", "graph", "Graph"]
            , simpleImport ["ohua", "graph", "Source"]
            , simpleImport ["ohua", "loader", "CodeGenHelper"]
            , simpleImport ["ohua", "util", "Lazy"]
            , simpleImport ["ohua", "Runtime"]
            , simpleImport
                  ["ohua", "runtime", "engine", "RuntimeProcessConfiguration"]
            , simpleImport
                  ["java", "util", "concurrent", "atomic", "AtomicReference"]
            ]
            [ ClassTypeDecl $
              ClassDecl
                  [Public, Abstract]
                  className
                  [] -- Generic type arguments go here
                  Nothing -- Superclass goes here
                  [] -- Implemented interfaces go here
               $
              ClassBody
                  [ InitDecl True $ mkStatefulFunctionLoadingCode finalOperators
                  , MemberDecl operatorsArrayField
                  , MemberDecl arcsArrayField
                  , MemberDecl $ MemberClassDecl preparedClassDecl
                  , MemberDecl $
                    MemberClassDecl $
                    configuredClassDecl className argumentAnnotations
                  , MemberDecl classConstructor
                  , MemberDecl configureFunctionDecl
                  , MemberDecl invokeFunctionDecl
                  ]
            ]
      where
        packageDecl
            | null nsList = Nothing
            | otherwise = Just $ PackageDecl $ Name $ map Ident nsList
        mkCommonArrayFieldWInit ref fieldName init =
            mkCommonArrayField
                ref
                fieldName
                (Just $ InitArray $ ArrayInit $ map InitExp init)
        operatorsArrayField =
            mkCommonArrayFieldWInit
                operatorClassRef
                opsFieldName
                (map newOp finalOperators)
        arcsArrayField =
            mkCommonArrayFieldWInit
                nonGenericArcClassRef
                arcsFieldName
                (replicate envArcCount (Lit Null) ++
                 addReturnCaptureArcs (map newArc localArcs))
        classConstructor =
            ConstructorDecl
                [Private]
                []
                className
                []
                []
                (ConstructorBody Nothing [])
        configureFunctionDecl =
            MethodDecl
                [Static, Final, Public]
                []
                (Just $
                 RefType $ ClassRefType $ ClassType [(configuredClassI, [])])
                configureMethodI
                [ FormalParam
                      [Final]
                      configurationType
                      False
                      (VarId configVarIdent)
                ]
                []
                Nothing $
            MethodBody $
            Just $
            Block
                [ BlockStmt $
                  Return $
                  Just $
                  InstanceCreation
                      []
                      (TypeDeclSpecifier $ ClassType [(configuredClassI, [])])
                      [ExpName $ Name [configVarIdent]]
                      Nothing
                ]
        invokeFunctionDecl :: MemberDecl
        invokeFunctionDecl =
            MethodDecl
                [Final, Static, Public]
                []
                returnType
                invokeMethodI
                invokeParams
                []
                Nothing $
            MethodBody $
            Just $
            Block $
            let defaultRuntimeOptions =
                    InstanceCreation
                        []
                        (TypeDeclSpecifier configurationClassType)
                        []
                        Nothing
                callConfigure =
                    MethodInv $
                    MethodCall (Name [configureMethodI]) [defaultRuntimeOptions]
                callPrepare =
                    MethodInv $
                    PrimaryMethodCall
                        callConfigure
                        []
                        prepareMethodI
                        (map (ExpName . Name . pure) invokeMethodArgNames)
                callInvoke =
                    MethodInv $
                    PrimaryMethodCall callPrepare [] invokeMethodI []
             in [BlockStmt $ Return $ Just callInvoke]

-- | Produces
-- @
--    static {
--              final CodeGenHelper.SfRef[] functions = { new CodeGenHelper.SfRef("ohua.lang", "capture"), ... };
--              CodeGenHelper.ensureFunctionsAreLoaded(functions);
--            }
-- @
-- from a list of operators
mkStatefulFunctionLoadingCode :: [Operator] -> Block
mkStatefulFunctionLoadingCode usedSfs =
    Block
        [ LocalVars
              [Final]
              (RefType $ ArrayType $ RefType $ ClassRefType sfRefHelperClass)
              [ VarDecl (VarId functionsArrayIdent) $
                Just $
                InitArray $ ArrayInit $ mkUsedStatefulFunctionsArray usedSfs
              ]
        , BlockStmt $
          ExpStmt $
          MethodInv $
          TypeMethodCall
              (Name [codeGenHelperClassI])
              []
              (Ident "ensureFunctionsAreLoaded")
              [ExpName (Name [functionsArrayIdent])]
        ]
  where
    functionsArrayIdent = Ident "functions"

-- | Produces the array initializer
-- @
--    { new CodeGenHelper.SfRef("ohua.lang", "capture"), ... }
-- @
-- from a list of operators
mkUsedStatefulFunctionsArray :: [Operator] -> [VarInit]
mkUsedStatefulFunctionsArray operators =
    [ InitExp $
    InstanceCreation
        []
        (TypeDeclSpecifier sfRefHelperClass)
        [ Lit $ String $ intercalate "." $ map (toString . unwrap) $ unwrap namespace
        , Lit $ String $ toString $ unwrap name_
        ]
        Nothing
    | QualifiedBinding namespace name_ <- nub $ map operatorType operators
    ]


-- | Produces the
-- @
--    return (Object) returnVar.get();
-- @
-- statement *iff* the return type is not @void@
invokeMethodReturnStatement :: Maybe Java.Type -> [BlockStmt]
invokeMethodReturnStatement Nothing = empty
invokeMethodReturnStatement (Just returnType) =
    [ BlockStmt $
      Return $
      Just $
      Cast returnType $
      MethodInv $
      PrimaryMethodCall (ExpName (Name [returnVarI])) [] (Ident "get") []
    ]

-- | Produces the
-- @
--   final Graph<Lazy<Object>> graph = new Graph<>(ops, arcs);
-- @
-- statement
createLocalGraph :: [BlockStmt]
createLocalGraph =
    [ LocalVars
          [Final]
          graphType
          [ VarDecl
                (VarId graphIdent)
                (Just $
                 InitExp $
                 InstanceCreation
                     []
                     (TypeDeclSpecifierUnqualifiedWithDiamond
                          graphClassI
                          Diamond)
                     [ ExpName $ Name $ pure opsFieldName
                     , ExpName $ Name $ pure arcsFieldName
                     ]
                     Nothing)
          ]
    ]
