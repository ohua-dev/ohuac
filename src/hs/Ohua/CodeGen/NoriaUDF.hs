module Ohua.CodeGen.NoriaUDF
    ( generateOperators
    , generate
    , suggestName
    , extraOperatorProcessing
    , rewriteQueryExpressions
    , mainArgsToTableRefs
    , rewriteFieldAccess
    , preResolveHook
    ) where

import Ohua.CodeGen.NoriaUDF.Operator
import Ohua.CodeGen.NoriaUDF.LowerToMir
