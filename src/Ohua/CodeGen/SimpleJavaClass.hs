{-# LANGUAGE NoOverloadedLists #-}
module Ohua.CodeGen.SimpleJavaClass (generate) where

import Protolude

import Text.Casing
import qualified Data.Text as T
import qualified Data.HashMap.Strict as HM
import Data.List (nub)
import Data.Version
import Language.Java.Syntax as Java
import Language.Java.Pretty (prettyPrint)

import Ohua.DFGraph
import Ohua.Types
import Ohua.ALang.NS
import Ohua.CodeGen.Iface
import qualified Ohua.Util.Str as Str

import Paths_ohuac

-- A hack for now, this should be shared later
tupleConstructor = TyRef $ Qual $ QualifiedBinding (unsafeMake []) "(,)"


generationInfoString :: LByteString
generationInfoString = "Generated with ohuac, version " <> toS (showVersion version)


stringifyQual :: QualifiedBinding -> [Char]
stringifyQual QualifiedBinding {..} =
    intercalate "." (map (Str.toString . unwrap) $ unwrap qbNamespace) <> "/" <>
    Str.toString (unwrap qbName)

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
                map ((, []) . Ident . Str.toString . unwrap) (unwrap ns) ++
                mkLast bnd
      where
        mkLast b = [(Ident $ Str.toString $ unwrap b, map ActualType l)]
    go l e =
        case e of
            TyRef ref -> formatRef ref l
            TyApp t1 t2 -> go (go [] t2 : l) t1

isVoidType :: TyExpr SomeBinding -> Bool
isVoidType = (== tupleConstructor)


generate :: CodeGen
generate CodeGenData {..} =
    pure
        ( T.intercalate "/" (map toS $ nsList ++ [classNameStr]) <> ".java"
        , toS (prettyPrint code) <> "\n//" <> generationInfoString <> "\n")
  where
    -- Values computed from CodeGenData
    nsList =
        map (toSnake . fromAny . Str.toString . unwrap) $
        unwrap entryPointNamespace
    classNameStr = toPascal $ fromAny $ Str.toString $ unwrap entryPointName
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
    argumentAnnotations =
        maybe
            (replicate entryPointArity objectType)
            (map tyExprToJava . argTypes)
            entryPointAnnotations
    localArcs = [a | a@Arc {source = LocalSource _} <- arcs graph]
    envArcs = [a | a@Arc {source = EnvSource _} <- arcs graph]
    envArcCount = length envArcs
    -- Name constants and functions
    opsFieldName = Ident "ops"
    arcsFieldName = Ident "arcs"
    indexToArgument = Ident . mappend "argument" . show
    indexToArgumentLazy = Ident . mappend "lazyArgument" . show
    returnVarI = Ident "returnVar"
    lazyI = Ident "Lazy"
    arcIdent = Ident "Arc"
    graphIdent = Ident "graph"
    -- Type constants
    objectI = Ident "Object"
    objectType = RefType objectRefType
    objectRefType = ClassRefType $ ClassType [(objectI, [])]
    operatorClassRef = ClassType [(Ident "Operator", [])]
    lazyObjectRefT =
        ClassRefType $
        ClassType
            [(lazyI, [ActualType $ ClassRefType $ ClassType [(objectI, [])]])]
    arcI = Ident "Arc"
    nonGenericArcClassRef = ClassType [(arcI, [])]
    graphClassI = Ident "Graph"
    codeGenHelperClassI = Ident "CodeGenHelper"
    sfRefHelperClass =
        ClassType [(codeGenHelperClassI, []), (Ident "SfRef", [])]
    -- Helpers
    isVoidFunction = isNothing returnType
    simpleImport path = ImportDecl False (Name $ map Ident path) False
    envSourceTypeDeclSpec =
        TypeDeclSpecifierWithDiamond
            (ClassType [(Ident "Source", [])])
            (Ident "Env")
            Diamond
    assignArcArray idx =
        ExpStmt .
        Assign
            (ArrayLhs $
             ArrayIndex
                 (ExpName (Name [arcsFieldName]))
                 [Lit $ Int $ toInteger idx])
            EqualA
    -- `new` expressions
    newTarget Target {..} =
        InstanceCreation
            []
            (TypeDeclSpecifier $ ClassType [(Ident "Target", [])])
            [ Lit $ Int $ toInteger $ unwrap operator
            , Lit $ Int $ toInteger index
            ]
            Nothing
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
            [ExpName $ Name $ pure $ indexToArgumentLazy idx]
            Nothing
    newOp Operator {..} =
        InstanceCreation
            []
            (TypeDeclSpecifier operatorClassRef)
            [ Lit $ Int $ toInteger $ unwrap operatorId
            , Lit $ String $ stringifyQual operatorType
            ]
            Nothing
    newArc Arc {..} =
        InstanceCreation
            []
            (TypeDeclSpecifierUnqualifiedWithDiamond arcIdent Diamond)
            [newTarget target, newSource source]
            Nothing
    createRealizedLazyExp val =
        MethodInv $
        TypeMethodCall (Name [lazyI]) [] (Ident "createRealized") [val]
    returnValueArc =
        newArc $
        Arc (Target retId 0) (LocalSource $ returnArc graph :: Source HostExpr)
    finalOperators
        | isVoidFunction = operators graph
        | otherwise = Operator retId "ohua.lang/capture" : operators graph
    addReturnCaptureArcs
        | isVoidFunction = identity
        | otherwise = (Lit Null :) . (returnValueArc :)
    code =
        CompilationUnit
            (if null nsList
                 then Nothing
                 else Just $ PackageDecl $ Name $ map Ident nsList)
            [ simpleImport ["ohua", "graph", "Arc"]
            , simpleImport ["ohua", "graph", "Operator"]
            , simpleImport ["ohua", "graph", "Target"]
            , simpleImport ["ohua", "graph", "Graph"]
            , simpleImport ["ohua", "graph", "Source"]
            , simpleImport ["ohua", "loader", "CodeGenHelper"]
            , simpleImport ["ohua", "util", "Lazy"]
            , simpleImport ["ohua", "Runtime"]
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
                  -- TODO load stateful functions
                  [ InitDecl True $
                    Block $
                    let functionsArrayIdent = Ident "functions"
                     in [ LocalVars
                              [Final]
                              (RefType $
                               ArrayType $
                               RefType $ ClassRefType sfRefHelperClass)
                              [ VarDecl (VarId functionsArrayIdent) $
                                Just $
                                InitArray $
                                ArrayInit
                                    [ InitExp $
                                    InstanceCreation
                                        []
                                        (TypeDeclSpecifier sfRefHelperClass)
                                        [ Lit $
                                          String $
                                          intercalate "." $
                                          map (Str.toString . unwrap) $
                                          unwrap namespace
                                        , Lit $
                                          String $ Str.toString $ unwrap name_
                                        ]
                                        Nothing
                                    | QualifiedBinding namespace name_ <-
                                          nub $ map operatorType finalOperators
                                    ]
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
                  , MemberDecl $
                    FieldDecl
                        [Private, Static, Final]
                        (RefType $
                         ArrayType $ RefType $ ClassRefType operatorClassRef)
                        [ VarDecl (VarId opsFieldName) $
                          Just $
                          InitArray $
                          ArrayInit (map (InitExp . newOp) finalOperators)
                        ]
                  , MemberDecl $
                    FieldDecl
                        [Private, Static, Final]
                        (RefType $
                         ArrayType $
                         RefType $ ClassRefType nonGenericArcClassRef)
                        [ VarDecl (VarId arcsFieldName) $
                          Just $
                          InitArray $
                          ArrayInit $
                          map InitExp $
                          replicate envArcCount (Lit Null) ++
                          addReturnCaptureArcs (map newArc localArcs)
                        ]
                  , MemberDecl $
                    ConstructorDecl
                        [Private]
                        []
                        className
                        []
                        []
                        (ConstructorBody Nothing [])
                  , MemberDecl $
                    MethodDecl
                        [Public, Static]
                        []
                        returnType
                        (Ident "invoke")
                        [ FormalParam [] ty False (VarId $ indexToArgument idx)
                        | (ty, idx) <- zip argumentAnnotations enumerateArgs
                        ]
                        []
                        Nothing $
                    MethodBody $
                    Just $
                    Block $
                    concat
                        [ do guard (not isVoidFunction)
                             let aRefId = Ident "AtomicReference"
                             pure $
                                 LocalVars
                                     [Final]
                                     (RefType $
                                      ClassRefType $
                                      ClassType
                                          [(aRefId, [ActualType objectRefType])])
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
                        , [ LocalVars
                                [Final]
                                (RefType lazyObjectRefT)
                                [ VarDecl (VarId $ indexToArgumentLazy idx) $
                                Just $
                                InitExp $
                                createRealizedLazyExp
                                    (ExpName $ Name $ pure $ indexToArgument idx)
                                | idx <- enumerateArgs :: [HostExpr]
                                ]
                          ]
                        , [ BlockStmt $ assignArcArray arcIdx (newArc arc)
                          | (arcIdx, arc) <- zip [0 ..] envArcs
                          ]
                        , do guard (not isVoidFunction)
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
                                             ExpName $ Name $ pure returnVarI
                                           ]
                                           Nothing
                                     ]
                                     Nothing
                        , [ LocalVars
                                [Final]
                                (RefType $
                                 ClassRefType $
                                 ClassType
                                     [ ( graphClassI
                                       , [ActualType lazyObjectRefT])
                                     ])
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
                          , BlockStmt $
                            ExpStmt $
                            MethodInv $
                            PrimaryMethodCall
                                (MethodInv $
                                 TypeMethodCall
                                     (Name [Ident "Runtime"])
                                     []
                                     (Ident "prepare")
                                     [ExpName $ Name $ pure graphIdent])
                                []
                                (Ident "run")
                                []
                          ]
                        , case returnType of
                              Nothing -> empty
                              Just t ->
                                  [ BlockStmt $
                                    Return $
                                    Just $
                                    Cast t $
                                    MethodInv $
                                    PrimaryMethodCall
                                        (ExpName (Name [returnVarI]))
                                        []
                                        (Ident "get")
                                        []
                                  ]
                        ]
                  ]
            ]
