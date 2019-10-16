module Ohua.CodeGen.Iface where

import Ohua.Prelude

import qualified Data.HashSet as Set

import Ohua.Standalone -- Used for TyAnnMap, that alias should be moved so I can
                       -- remove that dependency here
import Ohua.DFGraph
import qualified Ohua.DFGraph.File as GR

data CodeGenOpts = CodeGenOpts

data CodeGenData = CodeGenData
  { graph :: OutGraph
  , entryPointArity :: Int
  , sfDependencies :: Set.HashSet QualifiedBinding
  , annotations :: Maybe TyAnnMap
  , entryPoint :: QualifiedBinding
  }

cgDataToGrFile :: CodeGenData -> GR.GraphFile
cgDataToGrFile CodeGenData {..} =
    GR.GraphFile
        { GR.graph = graph
        , GR.sfDependencies = sfDependencies
        , GR.mainArity = entryPointArity
        }

type NameSuggester = QualifiedBinding -> Text

type CodeGen
     = forall m. ( MonadReader CodeGenOpts m
                 , MonadError Text m
                 , MonadLogger m
                 , MonadIO m
                 ) =>
                     CodeGenData -> m LByteString
