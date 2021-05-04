module Ohua.CodeGen.NoriaUDF.Mir where

import Data.Word
import qualified Ohua.DFGraph as DFGraph
import Ohua.Prelude
import Data.Text.Prettyprint.Doc as P
import Ohua.ALang.PPrint ()

-- | (isFromMain, Index)
data Column =
    Column
        { table :: Maybe Text
        , name :: Text
        }
    deriving (Show, Eq, Ord, Generic)

instance Pretty Column where
    pretty Column{..} = maybe "?" pretty table <> "." <> pretty name

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

instance Pretty Operator where
    pretty = \case
        Equal -> "="
        Less -> "<"
        LessOrEqual -> "<="
        Greater -> ">"
        GreaterOrEqual -> ">="
        NotEqual -> "!="

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

instance Pretty Value where
    pretty = \case
        ColumnValue c -> pretty c
        ConstantValue v -> pretty v

instance Hashable Value

instance NFData Value

data FilterCondition =
    Comparison Operator Value
    deriving (Show, Eq, Generic)

instance Pretty FilterCondition where
    pretty (Comparison op v) =
        pretty op <+> pretty v

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
