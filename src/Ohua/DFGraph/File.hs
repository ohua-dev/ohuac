module Ohua.DFGraph.File where

import Ohua.Prelude

import qualified Data.Set as Set

import Ohua.DFGraph

data GraphFile = GraphFile
    { graph :: OutGraph
    , mainArity :: Int
    , sfDependencies :: Set.Set QualifiedBinding
    } deriving (Eq, Show, Generic)
