module Ohua.CodeGen.NoriaUDF.Types where

import qualified Ohua.DFGraph as DFGraph
import Ohua.Helpers.Template (Substitutions, Template)
import Ohua.Prelude
import qualified Ohua.CodeGen.NoriaUDF.Mir as Mir

data GenerationType
    = TemplateSubstitution Template
                           FilePath
                           Substitutions
    | GenerateFile FilePath
                   Text

data ExecSem
    = One
    | Many

type ExecSemantic = (ExecSem, ExecSem)


    -- - | MirJoin
    -- - | MirProjection

data InternalColumn = InternalColumn
    { producingOperator :: Int
    , outputIndex :: Int
    } deriving (Show, Eq, Ord, Generic)

instance Hashable InternalColumn
instance NFData InternalColumn

type Column = InternalColumn

type SomeColumn = Either Column Mir.Column
-- instance Hashable Column
-- instance NFData Column
type Scope = GScope SomeColumn
data GScope col =
    GroupBy [col]
    deriving (Show, Eq, Generic)

instance Hashable a => Hashable (GScope a)
instance NFData a => NFData (GScope a)

data JoinType
    = FullJoin
    | InnerJoin [SomeColumn]
    deriving (Show, Eq, Generic)

instance NFData JoinType
instance Hashable JoinType

data Operator
    = CustomOp QualifiedBinding [(Int, SomeColumn)]
    | Join JoinType
    | Project [SomeColumn]
    | Identity
    | Sink
    | Source Word
    | Filter { conditions :: HashMap SomeColumn Mir.FilterCondition }
    deriving (Show, Eq, Generic)

-- instance Hashable Operator
instance NFData Operator


data OperatorDescription
    = Op_MIR (QualifiedBinding, Operator)
    | Op_UDF UDFDescription

data UDFDescription = UDFDescription
      { generations :: [GenerationType]
      , udfName :: QualifiedBinding
      , inputBindings :: [Binding]
      , udfState :: Maybe QualifiedBinding
      , referencedFields :: [Int]
      , execSemantic :: (ExecSem, ExecSem)
      }

type RegisterOperator = OperatorDescription -> IO ()
