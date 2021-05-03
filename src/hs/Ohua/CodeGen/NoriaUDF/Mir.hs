module Ohua.CodeGen.NoriaUDF.Mir where

import Data.Word
import qualified Ohua.DFGraph as DFGraph
import Ohua.Prelude

-- | (isFromMain, Index)
data Column =
    Column
        { table :: Maybe Text
        , name :: Text
        }
    deriving (Show, Eq, Ord, Generic)

instance Hashable Column

instance NFData Column

data ExecutionType
    = Reduction
          { groupBy :: [Column]
          }
    | Simple Word
  deriving (Show)

data Operator
    = Equal
    | Less
    | LessOrEqual
    | Greater
    | GreaterOrEqual
    | NotEqual
    deriving (Show, Eq, Ord, Generic)

instance Hashable Operator

instance NFData Operator

deMorganOp = \case
    Equal -> NotEqual
    NotEqual -> Equal
    Less -> GreaterOrEqual
    LessOrEqual -> Greater
    Greater -> LessOrEqual
    GreaterOrEqual -> Less


data Value
    = ColumnValue Column
    | ConstantValue Lit
    deriving (Show, Eq, Generic)

instance Hashable Value

instance NFData Value

data FilterCondition =
    Comparison Operator Value
    deriving (Show, Eq, Generic)

instance Hashable FilterCondition

instance NFData FilterCondition

data Node
    = Regular
          { nodeFunction :: QualifiedBinding
          , indices :: [Column]
          , executionType :: ExecutionType
          }
    | Join
          { mirJoinProject :: [Column]
          , left :: [Column]
          , right :: [Column]
          }
    | Identity [Column]
    | Filter
          { conditions :: [Maybe FilterCondition]
          }
  deriving (Show)
