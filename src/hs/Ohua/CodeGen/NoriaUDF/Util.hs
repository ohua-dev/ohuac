module Ohua.CodeGen.NoriaUDF.Util where

import Control.Exception
import qualified Prelude
import Prelude (($))
import GHC.Exception (CallStack, prettyCallStack )
import GHC.Stack (HasCallStack, callStack)

import Ohua.Prelude
import Ohua.ALang.Lang (Expr(..))

-- | Just a simple helper to make writing the HashMap literals nicer
(~>) :: a -> b -> (a, b)
a ~> b = (a, b)

infixl 4 ~>

data ErrorWithTrace = forall e . Exception e => ErrorWithTrace CallStack e

instance Exception ErrorWithTrace

instance Prelude.Show ErrorWithTrace where
    show (ErrorWithTrace trace e) =
        Prelude.unlines [Control.Exception.displayException e, "Stack Trace:", prettyCallStack trace]

throwStack :: ( HasCallStack, Exception e) => e -> a
throwStack e = Control.Exception.throw $ ErrorWithTrace callStack e

pattern OhuaFieldNS :: NSRef

pattern OhuaFieldNS <- ["ohua", "lang", "field"]
  where OhuaFieldNS = ["ohua", "lang", "field"]

pattern FieldE f <- Lit (FunRefLit (FunRef (QualifiedBinding OhuaFieldNS f) _))

pattern ReduceStateB :: QualifiedBinding
pattern ReduceStateB = "ohua.lang/reduceState"

pattern ReduceState :: Expr
pattern ReduceState <- Lit (FunRefLit (FunRef ReduceStateB _))
  where ReduceState = Lit (FunRefLit (FunRef ReduceStateB Nothing))


pattern PackStateB :: QualifiedBinding
pattern PackStateB = "ohua.lang/packState"

pattern PackState :: Expr
pattern PackState <- Lit (FunRefLit (FunRef PackStateB _))
  where PackState = Lit (FunRefLit (FunRef PackStateB Nothing))
