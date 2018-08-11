module Ohua.DFGraph.File where

import Protolude

import qualified Data.Set as Set

import Ohua.DFGraph
import Ohua.Types

data GraphFile = GraphFile
    { graph :: OutGraph
    , mainArity :: Int
    , sfDependencies :: Set.Set QualifiedBinding
    } deriving (Eq, Show, Generic)
