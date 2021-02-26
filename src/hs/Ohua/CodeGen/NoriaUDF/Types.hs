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

type Column = (Int, Int)

-- instance Hashable Column
-- instance NFData Column

data Scope =
    GroupBy [DFGraph.Target]
    deriving (Show, Eq, Generic)

-- instance Hashable Scope
instance NFData Scope

data Operator
    = CustomOp QualifiedBinding
    | Join { joinOn :: [Scope] }
    | Projection [Column]
    | Identity
    | Sink
    | Source Word Text
    | Filter { conditions :: HashMap (Either Column Mir.Column) Mir.FilterCondition }
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
