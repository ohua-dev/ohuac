module Ohua.CodeGen.Iface where

import Protolude

import qualified Data.Set as Set

import Ohua.Monad
import Ohua.Types
import Ohua.Standalone -- Used for TyAnnMap, that alias should be moved so I can
                       -- remove that dependency here
import Ohua.DFGraph
import qualified Ohua.DFGraph.File as GR
import qualified Ohua.Util.Str as Str

data CodeGenOpts = CodeGenOpts

data CodeGenData = CodeGenData
  { graph :: OutGraph
  , entryPointArity :: Int
  , sfDependencies :: Set.Set QualifiedBinding
  , annotations :: Maybe TyAnnMap
  , entryPointName :: Binding
  , entryPointNamespace :: NSRef
  }

cgDataToGrFile :: CodeGenData -> GR.GraphFile
cgDataToGrFile CodeGenData {..} =
    GR.GraphFile
        { GR.graph = graph
        , GR.sfDependencies = sfDependencies
        , GR.mainArity = entryPointArity
        }

type NameSuggester = Text

type CodeGen
     = forall m. ( MonadReader CodeGenOpts m
                 , MonadError Str.Str m
                 , MonadLogger m
                 , MonadIO m
                 ) =>
                     CodeGenData -> m (NameSuggester, LByteString)
