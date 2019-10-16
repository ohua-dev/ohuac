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

suggestName :: NameSuggester
suggestName bnd = unwrap $ bnd ^. name <> ".ohuao"

generate :: CodeGen
generate cgdf =
    pure $ encode $ cgDataToGrFile cgdf
