module Ohua.DFGraph.File where

import Ohua.Prelude

import qualified Data.HashSet as Set

import Ohua.DFGraph

data GraphFile = GraphFile
    { graph :: OutGraph
    , mainArity :: Int
    , sfDependencies :: Set.HashSet QualifiedBinding
    } deriving (Eq, Show, Generic)
