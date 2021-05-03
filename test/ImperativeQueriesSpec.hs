{-# LANGUAGE QuasiQuotes #-}
module ImperativeQueriesSpec where

import Test.Hspec
import Ohua.Prelude
import Ohua.ALang.Refs

import TestUtil

spec :: Spec
spec = do
    imperativeRewrites


type Transform = Text -> a

-- | Transform imperative manipulations to single assignment form
tSSA :: Transform
tSSA = undefined

-- | Transform Loops into folds
tFold :: Transform
tFold = undefined

fold lam z coll = "ohua.lang/fold" `Apply` lam `Apply` z `Apply` coll

tup2 one two = "ohua.lang/(,)" `Apply` one `Apply` two

imperativeRewrites :: Spec
imperativeRewrites = do
    describe "imperative rewrites" $ do
        it "transforms the nop loop" $
            tFold [str|
let s = Table::new();
for x in q {
    s.add(x):
}
s
            |]
            `shouldBe`
            alang [str|
let s = Table::new();
let ((), s0) = fold(|x, s | ((), s.add(x)), s, q);
s0
                      |]
        it "performs SSA " $ do
            tSSA [str|
let s = Table::new();
s.add(x);
s.add(y);
s
                  |]
            `shouldBe`
            alang [str|
let s = Table::new();
let ((), s1) = s.add(x);
let ((), s2) = s.add(y);
s2
                      |]
