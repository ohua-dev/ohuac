module Ohua.CodeGen.NoriaUDF.Types where

import qualified Ohua.DFGraph as DFGraph
import Ohua.Helpers.Template (Substitutions, Template)
import Ohua.Prelude hiding (Identity)
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Text.Prettyprint.Doc ((<+>), pretty)
import qualified Ohua.CodeGen.NoriaUDF.Mir as Mir
import Data.Text.Prettyprint.Doc ((<+>), pretty)
import qualified Data.HashMap.Strict as HashMap

data NType
    = NTSeq NType
    | NTTup [NType]
    | NTRecFromTable Binding
    | NTAnonRec Binding [(Binding, NType)]
    | NTScalar InternalColumn
  deriving (Show, Eq, Ord, Generic)

instance Hashable NType
instance NFData NType

instance PP.Pretty NType where
    pretty = \case
        NTSeq s -> "Seq<" <> (pretty s) <> ">"
        NTTup ts -> PP.tupled (map pretty ts)
        NTRecFromTable r -> "Record<" <> pretty r <> ">"
        NTAnonRec b rs -> pretty b <>
            PP.encloseSep PP.lbracket PP.rbracket PP.comma
            (map (\(f, t) -> pretty f <+> PP.colon <+> pretty t) rs)
        NTScalar InternalColumn {..} -> "FromOp<" <> pretty producingOperator <> PP.comma <+> pretty outputIndex <> ">"

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
    = CustomOp QualifiedBinding [SomeColumn]
    | Join JoinType
    | Project [SomeColumn]
    | Identity
    | Sink
    | Source Word
    | Filter { conditions :: HashMap SomeColumn Mir.FilterCondition, arguments :: (Binding, [Binding]) }
    deriving (Show, Eq, Generic)

-- instance Hashable Operator
instance NFData Operator


instance PP.Pretty Operator where
    pretty = \case
        Filter conds _ ->
            "σ" <+>
            PP.list
            [ showCol col <+> PP.pretty cond
            | (col, cond) <- HashMap.toList conds]
        Join t ->
            case t of
                FullJoin -> "><"
                InnerJoin c -> "⋈" <+> PP.list (map showCol c)
        Identity -> "≡"
        Sink -> "Sink"
        Source s -> "B" <+> PP.pretty s
        Project c -> "π" <+> PP.list (map showCol c)
        CustomOp o c -> PP.pretty o <+> PP.list (map showCol c)
      where
          showCol = \case
              Left InternalColumn{..} -> PP.pretty producingOperator <> ":" <> PP.pretty outputIndex
              Right c -> PP.pretty c

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
