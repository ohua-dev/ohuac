module Ohua.CodeGen.NoriaUDF.Util where

-- | Just a simple helper to make writing the HashMap literals nicer
(~>) :: a -> b -> (a, b)
a ~> b = (a, b)

infixl 4 ~>
