{-# LANGUAGE CPP, TemplateHaskell, DataKinds #-}
module Ohua.Stdlib (stdlib) where

import Ohua.Prelude

import GHC.TypeLits as TL
import qualified Data.ByteString.Lazy as LB (readFile)
import qualified Language.Haskell.TH.Syntax as TH (lift, addDependentFile)
import Control.Lens ((^..), to, foldMapOf)
import qualified Data.HashSet as HS

import Ohua.ALang.Lang
import Ohua.Frontend.Lang (toAlang, definedBindings)
import Ohua.Frontend.NS
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
       in do
             TH.addDependentFile stdlibFileName
             bytes <- liftIO (LB.readFile stdlibFileName)
             let flang = parseMod bytes
             ns <- fmap (either error id) $ runExceptT $ do
                 alang <- runGenBndT (foldMapOf (decls . traverse) definedBindings flang) $ (decls . traverse) toAlang flang
                 resolveNS ifacem alang
             TH.lift  ns)
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
