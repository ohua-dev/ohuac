module Ohua.CodeGen.NoriaUDF.Util where

import Control.Exception
import qualified Prelude
import Prelude (($))
import GHC.Exception (CallStack, prettyCallStack )
import GHC.Stack (HasCallStack, callStack)

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
