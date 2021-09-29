module Ohua.CodeGen.NoriaUDF.Types where

import qualified Data.Binary as B
import qualified Ohua.DFGraph as DFGraph
import Ohua.Helpers.Template (Substitutions, Template)
import Ohua.Prelude hiding (Identity)
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Text.Prettyprint.Doc ((<+>), pretty)
import qualified Ohua.CodeGen.NoriaUDF.Mir as Mir
import Data.Text.Prettyprint.Doc ((<+>), pretty)
import qualified Data.HashMap.Strict as HashMap
import Control.Lens.Plated (Plated, plate, gplate)

data NType
    = NTSeq NType
    | NTTup [NType]
    | NTRecFromTable Mir.Table
    | NTAnonRec Binding NTFields
    | NTScalar SomeColumn
  deriving (Show, Eq, Ord, Generic)

instance Plated NType where
    plate = gplate

isRecNType, isSeqNType, isUnitNType :: NType -> Bool

isRecNType = \case
    NTAnonRec {} -> True
    NTRecFromTable {} -> True
    _ -> False

isSeqNType = \case
    NTSeq {} -> True
    _ -> False

isUnitNType = \case
    NTTup [] -> True
    _ -> False

shallowEqNType :: NType -> NType -> Bool
shallowEqNType NTSeq {} NTSeq {} = True
shallowEqNType NTTup {} NTTup {} = True
shallowEqNType NTScalar {} NTScalar {} = True
shallowEqNType t1 t2 = isRecNType t1 && isRecNType t2

type NTFields = [(Binding, NType)]

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
        NTScalar (Left InternalColumn {..}) -> "FromOp<" <> pretty producingOperator <> PP.comma <+> pretty outputIndex <> ">"
        NTScalar (Right c) -> pretty c

data GenerationType
    = TemplateSubstitution Template
                           FilePath
                           Substitutions
    | GenerateFile FilePath
                   Text
    deriving (Eq, Generic)


data ExecSem
    = One
    | Many
    deriving (Eq, Generic)

type ExecSemantic = (ExecSem, ExecSem)


    -- - | MirJoin
    -- - | MirProjection

data InternalColumn = InternalColumn
    { producingOperator :: Int
    , outputIndex :: Int
    } deriving (Show, Eq, Ord, Generic)


type Column = InternalColumn

instance PP.Pretty InternalColumn where
    pretty InternalColumn{..} = pretty producingOperator <> ":" <> pretty outputIndex

type SomeColumn = Either Column Mir.Column
-- instance Hashable Column
-- instance NFData Column
type Scope = GScope SomeColumn
data GScope col =
    GroupBy [col]
    deriving (Show, Eq, Generic)

data JoinType
    = FullOuterJoin
    | LeftOuterJoin
    | InnerJoin
    deriving (Show, Eq, Generic)

data CtrlType
    = SmapCtrl
    | IfCtrl { iAmTrueBranch :: Bool, conditionColumn :: SomeColumn }
    deriving (Generic, Eq, Ord, Show)

type ProjectColSpec = Either (InternalColumn, Mir.DataType ) SomeColumn

data Operator
    = CustomOp { opName :: QualifiedBinding, opInputs :: [Either Mir.DataType SomeColumn] }
    | Join { joinType :: JoinType, joinOn :: [(SomeColumn, SomeColumn)] }
    | Project { projectEmit :: [ProjectColSpec]}
    | Identity
    | Sink
    | Source Mir.Table
    | Filter { conditions :: HashMap SomeColumn ( Mir.FilterCondition Mir.Column), arguments :: (Binding, [Binding]) }
    | IsEmptyCheck
    | Select SelectPayload
    | Ctrl Int CtrlType
    deriving (Show, Eq, Generic)

type SelectPayload = [[Either SomeColumn Mir.Table]]

-- instance Hashable Operator


instance PP.Pretty Operator where
    pretty = \case
        Select sides -> "⋃" <+> PP.list (map (PP.list . map (either showCol PP.pretty)) sides)
        Filter conds _ ->
            "σ" <+>
            PP.list
            [ showCol col <+> PP.pretty cond
            | (col, cond) <- HashMap.toList conds]
        Join t on -> pretty t <+> PP.list (map (\(c1, c2) -> showCol c1 <+> "=" <+> showCol c2) on)
        Identity -> "≡"
        Sink -> "Sink"
        Source s -> "B" <+> PP.pretty s
        Project {..} -> "π" <+> PP.list (map (either pretty showCol ) projectEmit)
        CustomOp o c -> PP.pretty o <+> PP.list (map (either pretty showCol ) c)
        IsEmptyCheck -> "∅?"
        Ctrl _ ty -> "ctrl" <> PP.parens (if ty == SmapCtrl then "smap" else "if")
      where
          showCol = \case
              Left InternalColumn{..} -> PP.pretty producingOperator <> ":" <> PP.pretty outputIndex
              Right c -> PP.pretty c

instance PP.Pretty JoinType where
    pretty = \case
        FullOuterJoin -> "><"
        LeftOuterJoin -> "⋊"
        InnerJoin -> "⋈"

data OperatorDescription
    = Op_MIR (QualifiedBinding, Operator)
    | Op_UDF UDFDescription
    deriving (Eq, Generic)

data UDFDescription = UDFDescription
      { generations :: [GenerationType]
      , udfName :: QualifiedBinding
      , inputBindings :: [Binding]
      , udfState :: Maybe (QualifiedBinding, [Lit])
      , referencedFields :: [Int]
      , execSemantic :: (ExecSem, ExecSem)
      } deriving (Eq, Generic)

type RegisterOperator = OperatorDescription -> IO ()


instance B.Binary GenerationType
instance B.Binary UDFDescription
instance B.Binary Operator
instance B.Binary CtrlType
instance B.Binary OperatorDescription
instance NFData CtrlType
instance NFData Operator
instance NFData JoinType
instance Hashable JoinType
instance Hashable a => Hashable (GScope a)
instance NFData a => NFData (GScope a)
instance Hashable InternalColumn
instance NFData InternalColumn
instance B.Binary JoinType
instance B.Binary InternalColumn
instance B.Binary ExecSem

instance (Eq a, Hashable a, B.Binary a, B.Binary b) => B.Binary (HashMap a b) where
    put = B.put . HashMap.toList
    get = HashMap.fromList <$> B.get
