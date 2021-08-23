module Ohua.CodeGen.NoriaUDF.Mir where

import qualified Data.Binary as B

import Data.Word
import qualified Ohua.DFGraph as DFGraph
import Ohua.Prelude hiding (list, Identity)
import Data.Text.Prettyprint.Doc as P hiding (list)
import Ohua.ALang.PPrint ()
import Control.Exception (throw)

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
  deriving (Show, Eq, Generic)

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
    | ConstantValue DataType
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

data DataType
    = None
    | Int Integer
    deriving (Show, Eq, Generic)

instance Num DataType where
    fromInteger = Int

data LiteralNotSupported = LiteralNotSupported Lit deriving (Show)

instance Exception LiteralNotSupported

litToDataType :: Lit -> DataType
litToDataType (NumericLit n) = Int n
litToDataType other = throw $ LiteralNotSupported other

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
          , isLeftJoin :: Bool
          }
    | Identity [Column]
    | Filter
          { -- conditions :: [(Word, FilterCondition Word)] -- in 0.7
            conditions :: [Maybe (FilterCondition Word)] -- in 0.1.2
          }
    | Union
      { mirUnionEmit :: [[Column]] }
    | Project { projectEmit :: [Column], projectLiterals :: [(Text, DataType)]}
  deriving (Show, Eq, Generic)

instance Pretty Node where
    pretty = \case
        Regular {..} -> pretty nodeFunction <+> list (map pretty indices)
        Join {..} ->  list (map pretty left) <+> "⋈"  <+> list (map pretty right) <+> "→" <+> list (map pretty mirJoinProject)
        Identity cols -> "≡" <+> list (map pretty cols)
        Filter conds -> "σ" <+> list [pretty (idx :: Word) <+> pretty cond | (idx, Just cond) <- zip [0..] conds]
        Union emit ->  "∪" <+> list [pretty c | lc <- emit, c <- lc]
        Project {} -> "π"


instance B.Binary DataType
instance B.Binary a => B.Binary (Value a)
instance B.Binary Operator
instance B.Binary col => B.Binary (FilterCondition col)
instance B.Binary ExecutionType
instance B.Binary Node
instance B.Binary Table
instance B.Binary Column
instance B.Binary HostExpr
instance B.Binary FnId
instance B.Binary FunRef
instance B.Binary Lit
instance B.Binary NSRef where
    put = B.put . unwrap
    get = makeThrow <$> B.get
instance B.Binary Binding
instance B.Binary QualifiedBinding

instance NFData DataType

instance Hashable DataType
instance Pretty DataType where
    pretty =
        \case
            None -> "None"
            Int i -> "Int" <> P.parens (pretty i)
