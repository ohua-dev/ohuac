{-# LANGUAGE CPP, TemplateHaskell, DataKinds #-}
module Ohua.Stdlib (stdlib) where

import Ohua.Prelude

import GHC.TypeLits as TL
import qualified Data.ByteString.Lazy as LB (readFile)
import qualified Language.Haskell.TH.Syntax as TH (lift, addDependentFile)

import Ohua.ALang.Lang
import Ohua.ALang.NS
import Ohua.Standalone

#if WITH_ML_PARSER
import Ohua.Compat.ML.Parser (parseMod)
#endif


#if WITH_STDLIB
#if WITH_ML_PARSER
stdlib :: Namespace Expression
stdlib =
    $(let ifacem = mempty -- TODO check this is correct
          stdlibFileName = "src/ohuac/ohua/std.ohuaml"
       in TH.addDependentFile stdlibFileName >>
          liftIO (LB.readFile stdlibFileName) >>=
          either (fail . toString) pure . resolveNS ifacem . parseMod >>=
          TH.lift)
#else
stdlib ::
       TypeError (TL.Text "The ML parser must be enabled to use the standard library.")
    => Namespace Expression
stdlib = error "impossible"

#endif
#else
stdlib :: Namespace Expression
stdlib = emptyNamespace ["ohua", "std"]
#endif
