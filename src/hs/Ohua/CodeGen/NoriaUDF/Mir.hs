module Ohua.CodeGen.NoriaUDF.Mir where

import Data.Word
import qualified Ohua.DFGraph as DFGraph
import Ohua.Prelude hiding (list, Identity)
import Data.Text.Prettyprint.Doc as P hiding (list)
import Ohua.ALang.PPrint ()

list = brackets . concatWith (surround ", ")

data Table = TableByIndex Word | TableByName Text
    deriving (Show, Eq, Ord, Generic)

instance Hashable Table
instance NFData Table

instance Pretty Table where
    pretty = \case
        TableByIndex i -> pretty i
        TableByName t -> pretty t

-- | (isFromMain, Index)
data Column =
    Column
        { table :: Maybe Table
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


data Value col
    = ColumnValue col
    | ConstantValue Lit
    deriving (Show, Eq, Generic)

instance Pretty col => Pretty ( Value col) where
    pretty = \case
        ColumnValue c -> pretty c
        ConstantValue v -> pretty v

instance Hashable col => Hashable ( Value col )

instance NFData col => NFData ( Value col )

data FilterCondition col =
    Comparison Operator ( Value col)
    deriving (Show, Eq, Generic)

instance Pretty col => Pretty ( FilterCondition col ) where
    pretty (Comparison op v) =
        pretty op <+> pretty v

instance Hashable col => Hashable (FilterCondition col)

instance NFData col => NFData ( FilterCondition col )

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
          { -- conditions :: [(Word, FilterCondition Word)] -- in 0.7
            conditions :: [Maybe (FilterCondition Word)] -- in 0.1.2
          }
    | Union
      { mirUnionEmit :: [[Column]] }
  deriving (Show)

instance Pretty Node where
    pretty = \case
        Regular {..} -> pretty nodeFunction <+> list (map pretty indices)
        Join {..} ->  list (map pretty left) <+> "⋈"  <+> list (map pretty right) <+> "→" <+> list (map pretty mirJoinProject)
        Identity cols -> "≡" <+> list (map pretty cols)
        Filter conds -> "σ" <+> list [pretty (idx :: Word) <+> pretty cond | (idx, Just cond) <- zip [0..] conds]
        Union emit ->  "∪" <+> list [pretty c | lc <- emit, c <- lc]
