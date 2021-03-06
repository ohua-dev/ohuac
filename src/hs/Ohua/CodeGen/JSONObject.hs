{-# OPTIONS_GHC -fno-warn-orphans #-}
module Ohua.CodeGen.JSONObject where

import Ohua.Prelude

import Data.Aeson

import Ohua.DFGraph.File
import Ohua.Serialize.JSON ()
import Ohua.CodeGen.Iface

instance ToJSON GraphFile where
    toEncoding = genericToEncoding defaultOptions
instance FromJSON GraphFile where
    parseJSON = genericParseJSON defaultOptions


generate :: CodeGen
generate cgdf@CodeGenData {entryPointName} =
    pure (unwrap $ entryPointName <> ".ohuao", encode $ cgDataToGrFile cgdf)
