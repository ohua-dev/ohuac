module Ohua.Helpers.Graph
    (module Data.Graph.Inductive
    , adjustNLabel
    , listTopo
    , listTopoFrom
    , lnmap
    ) where

import Ohua.Prelude

import Data.Graph.Inductive
import qualified Data.Graph.Inductive.PatriciaTree as P
import qualified Data.IntSet as IS
import qualified Data.IntMap as IM

unGr :: Gr a b -> P.GraphRep a b
unGr (P.Gr g) = g

adjustNLabel :: (a -> a) -> Node -> Gr a b -> Gr a b
adjustNLabel f n = P.Gr . IM.adjust (_2 %~ f) n . unGr


listTopoFrom :: Graph g => [ Node ] -> g a b -> [Node]
listTopoFrom inits gr = go inits $ IS.fromList inits
  where
    go stage visited =
        stage ++ go next (IS.intersection visited $ IS.fromList next)
      where
        next =
            stage >>=
            filter (all (flip IS.member visited) . pre gr) . suc gr

listTopo :: Graph g => g a b -> [Node]
listTopo gr = listTopoFrom (filter (null . pre gr) (nodes gr)) gr


lnmap :: (LNode a -> a') -> Gr a b -> Gr a' b
lnmap f = P.Gr . IM.mapWithKey (\k -> _2 %~ f . (k,) ) . unGr
