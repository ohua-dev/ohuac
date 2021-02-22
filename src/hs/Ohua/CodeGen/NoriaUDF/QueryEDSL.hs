{-# LANGUAGE TemplateHaskell, StandaloneDeriving #-}

module Ohua.CodeGen.NoriaUDF.QueryEDSL where

import Control.Lens.TH
import Data.Functor.Foldable
import qualified Data.HashMap.Strict as HashMap
import Ohua.ALang.Lang
import Ohua.ALang.PPrint (quickRender)
import qualified Ohua.CodeGen.NoriaUDF.Mir as Mir
import Ohua.CodeGen.NoriaUDF.Types
import Ohua.CodeGen.NoriaUDF.Util
import Ohua.Prelude
import Ohua.Unit

exprToMirCondition ::
       Expr
    -> OhuaM env (HashMap.HashMap (Either Column Mir.Column) Mir.FilterCondition)
exprToMirCondition (Lambda table body) = pure $ HashMap.fromList $ apo f body
  where
    toCond (Lit (FunRefLit (FunRef (QualifiedBinding ["ohua", "lang"] o) _)) `Apply` left `Apply` right) =
        (Right baseCol, Mir.Comparison actualOp val)
      where
        op =
            case o of
                "eq" -> Mir.Equal
                other -> error $ "Unknown operator " <> quickRender other
        (actualOp, baseCol, val) =
            case (toVal left, toVal right) of
                (Mir.ColumnValue c, other) -> (op, c, other)
                (other, Mir.ColumnValue c) -> (flipOp op, c, other)
                other ->
                    error $
                    "Unexpectedly no column in this filter: " <> showT other
    toCond other = error $ "can't convert " <> quickRender other
    toVal (t `BindState` Lit (FunRefLit (FunRef (QualifiedBinding ["ohua", "lang", "field"] n) _))) =
        assert (t == Var table) $
        Mir.ColumnValue (Mir.Column Nothing (unwrap n))
    toVal (Lit l) = Mir.ConstantValue l
    toVal other = error $ "can't convert " <> quickRender other
    flipOp =
        \case
            Mir.Equal -> Mir.Equal
    f (Lit (FunRefLit (FunRef o _)) `Apply` left `Apply` right)
        | o == "ohua.lang/&&" = Cons (toCond left) $ Right right
    f other = Cons (toCond other) (Left [])
exprToMirCondition other = error $ "can't convert " <> quickRender other

type EDSLRewrite env = (RegisterOperator -> Expr -> [Expr] -> OhuaM env Expr)

queryEDSL :: QualifiedBinding -> Maybe (EDSLRewrite env)
queryEDSL = flip HashMap.lookup table
  where
    fn f = QualifiedBinding ["ohua", "sql", "query"] f
    table :: HashMap QualifiedBinding (EDSLRewrite env)
    table =
        [ fn "select" ~>
          ((\_ state args -> assertM (null args) >> pure state) :: EDSLRewrite env)
         -- eventually this should insert a remapping and field selection node
        , fn "where_" ~>
          ((\register state args -> do
                let arg = case args of
                        [arg] -> arg
                        other -> error $ "too many argument " <> quickRender other
                conditionMap <- exprToMirCondition arg
                name <- generateBindingWith "where_"
                let newFnName =
                        QualifiedBinding ["ohua", "generated", "sql_ops"] name
                liftIO $ register $ Op_MIR (newFnName, Filter conditionMap)
                pure $ Apply (embedE newFnName) state) :: EDSLRewrite env)
         -- should resolve to the base state to figure out the table this references
        ]
