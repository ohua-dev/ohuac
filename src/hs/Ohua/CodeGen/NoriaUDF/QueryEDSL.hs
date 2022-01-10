{-# LANGUAGE TemplateHaskell, StandaloneDeriving #-}

module Ohua.CodeGen.NoriaUDF.QueryEDSL where

import Control.Lens.TH
import Data.Functor.Foldable
import qualified Data.HashMap.Strict as HashMap
import Ohua.ALang.Lang
import Ohua.ALang.PPrint (Pretty, quickRender)
import Ohua.ALang.Util (fromListToApply)
import qualified Ohua.CodeGen.NoriaUDF.Mir as Mir
import Ohua.CodeGen.NoriaUDF.Types
import Ohua.CodeGen.NoriaUDF.Util
import Ohua.Prelude
import Ohua.Unit
import Control.Monad.Writer
import qualified Control.Lens.Plated as Plated
import Control.Lens (at, ix)

pattern BuiltinFunE b <- Lit (FunRefLit (FunRef (QualifiedBinding ["ohua", "lang"] b) _))

data Conjunction = And | Or deriving (Show, Eq, Ord)

data Condition = Comp (Either Column Mir.Column, Mir.FilterCondition Mir.Column) | Conj Conjunction Condition Condition
    deriving (Show, Eq, Generic)

instance Plated.Plated Condition where
    plate = Plated.gplate

exprToMirCondition ::
    Binding
    -> Expr
    -> OhuaM env (HashMap.HashMap (Either Column Mir.Column) ( Mir.FilterCondition Mir.Column), [Binding])
exprToMirCondition tab (Lambda table body) =
    pure $ first HashMap.fromList $ runWriter $ flip runReaderT HashMap.empty $ fmap andToList $ f body
  where
    mkE :: (HasCallStack , Pretty a) => a -> b
    mkE t = error $ "Cannot convert \"" <> quickRender t <> "\" in " <> quickRender body
    toVal (Var v `BindState` FieldE n) = do
        v' <- if (v == table)
            then pure tab
            else tell [v] >> pure v
        pure $ Mir.ColumnValue (Mir.Column (Just $ Mir.TableByName $ unwrap v') (unwrap n))
    toVal (Lit l) = pure $ Mir.ConstantValue $ Mir.litToDataType l
    toVal other = mkE other
    flipOp =
        \case
            Mir.Equal -> Mir.Equal
            Mir.NotEqual -> Mir.NotEqual
            other -> Mir.deMorganOp other -- Not sure this is actually true, I'm just lazy
    f (Let bnd mexp mbod) = do
        exp <- f mexp
        local (at bnd .~ Just exp) $ f mbod
    f (Var v) = fromMaybe (error $ "Variable " <> quickRender v <> " not found locally. Variables from scope are not yet supported.")  <$>
        asks (^? ix v)
    f (BuiltinFunE b `Apply` left `Apply` right)
        | Just conj <- (case b of "and" -> Just And; "or" -> Just Or; _ -> Nothing) =
              Conj conj <$> f left <*> f right
        | otherwise = do
              vl <- toVal left
              vr <- toVal right
              let (actualOp, baseCol, val) =
                      case (vl, vr) of
                          (Mir.ColumnValue c, other) -> (op, c, other)
                          (other, Mir.ColumnValue c) -> (flipOp op, c, other)
                          other ->
                              error $
                              "Unexpectedly no column in this filter: " <> showT other
              pure $ Comp (Right baseCol, Mir.Comparison actualOp val)
                where
                  op =
                      case b of
                          "eq" -> Mir.Equal
                          "neq" -> Mir.NotEqual
                          "geq" -> Mir.GreaterOrEqual
                          "gt" -> Mir.Greater
                          "lt" -> Mir.Less
                          "leq" -> Mir.LessOrEqual
                          other -> error $ "Unknown operator " <> quickRender other
    f (BuiltinFunE "not" `Apply` thing) = deMorgan <$> f thing
    f other =
        toVal other >>= \case
            Mir.ColumnValue c -> pure $ Comp (Right c, Mir.Comparison Mir.Equal $ Mir.ConstantValue 1)
            _ -> mkE other
    deMorgan = transform $ \case
        (Conj con a b) -> Conj (deMorganConjunction con) a b
        (Comp (c, Mir.Comparison op v)) -> Comp (c, Mir.Comparison (Mir.deMorganOp op) v)
    deMorganConjunction = \case And -> Or; Or -> And
    andToList = Plated.para f'
      where
        f' (Conj op _ _) sub
            | op == Or = error $ "Disjunction not supported like this " <> quickRender body
            | otherwise = concat sub
        f' (Comp v) [] = [v]
exprToMirCondition _ other = error $ "can't convert " <> quickRender other

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
        , fn "filter" ~>
          ((\register stArg args -> do
                state <- generateBindingWith "where_state"
                let arg = case args of
                        [arg] -> arg
                        other -> error $ "too many argument " <> quickRender other
                (conditionMap, free)  <- exprToMirCondition state arg
                name <- generateBindingWith "where_"
                let newFnName =
                        QualifiedBinding ["ohua", "generated", "sql_ops"] name
                liftIO $ register $ Op_MIR (newFnName, Filter conditionMap (state, free))
                pure $ Let state stArg $ fromListToApply (FunRef newFnName Nothing) (Var state : map Var free)) :: EDSLRewrite env)
         -- should resolve to the base state to figure out the table this references
        ]

rewriteFieldAccess :: Expr -> OhuaM env Expr
rewriteFieldAccess = pure . t
  where
    t = rewrite $ \case
        BindState s f@(FieldE _) ->
            Just $ f `Apply` s
        _ -> Nothing
