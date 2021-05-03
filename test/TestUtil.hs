module TestUtil where

import Prelude ((.), pure)
import Language.Haskell.TH.Quote
import Language.Haskell.TH
import Ohua.Compat.Clike.Parser
import Ohua.Compat.Clike.Types

str :: QuasiQuoter
str = QuasiQuoter
    { quoteExp = pure . LitE . StringL }
