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
import Control.Lens.Plated (Plated, plate, gplate, para)
import Prelude (show)

data NType
    = NTSeq NType
    | NTTup [NType]
    | NTRecFromTable Mir.Table
    | NTAnonRec Binding NTFields
    | NTScalar (Mir.Value SomeColumn)
  deriving (Eq, Ord, Generic)

instance Plated NType where
    plate f = \case
        NTTup t -> NTTup <$> traverse f t
        NTAnonRec name flds -> NTAnonRec name . zip (map fst flds) <$> traverse (f . snd) flds
        a -> gplate f a

typeToCols :: (Mir.Table -> [Mir.Column]) -> [NType] -> [SomeColumn]
typeToCols tableExpansion = (>>= para g)
  where
    g a r = case a of
        NTRecFromTable t -> map Right $ tableExpansion t
        NTAnonRec _ f -> assert (length f == length r) $ concat r
        NTScalar (Mir.ColumnValue s) -> [s]
        _ -> concat r

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
    NTScalar (Mir.ConstantValue Mir.None) -> True
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
        NTScalar s ->
            case s of
                Mir.ColumnValue c ->
                    case c of 
                        Left InternalColumn {..} -> "FromOp<" <> pretty producingOperator <> PP.comma <+> pretty outputIndex <> ">"
                        Right c -> pretty c
                Mir.ConstantValue c -> pretty c

instance Show NType where
    show = toString . quickRender

data GenerationType
    = TemplateSubstitution Template
                           FilePath
                           Substitutions
    | GenerateFile FilePath
                   Text
    deriving (Eq, Generic)

instance Show GenerationType where 
    show = \case 
        TemplateSubstitution tpl p _ -> "TemplateSubstitution(" <> tpl <> " -> " <> p <> ")"
        GenerateFile p _ -> "GenerateFile(" <> p <> ")"


data ExecSem
    = One
    | Many
    deriving (Eq, Generic,Show)

type ExecSemantic = (ExecSem, ExecSem)


    -- - | MirJoin
    -- - | MirProjection

data InternalColumn = InternalColumn
    { producingOperator :: Int
    , outputIndex :: Int
    } deriving (Eq, Ord, Generic)


type Column = InternalColumn

instance PP.Pretty InternalColumn where
    pretty InternalColumn{..} = "op:" <> pretty producingOperator <+> "idx:" <> pretty outputIndex

instance Show InternalColumn where
    show = toString . quickRender

type SomeColumn = Either Column Mir.Column
-- instance Hashable Column
-- instance NFData Column
type Scope = GScope SomeColumn
data GScope col =
    GroupBy [col]
    deriving (Show, Eq, Generic)

data CtrlType
    = SmapCtrl
    | IfCtrl { iAmTrueBranch :: Bool, conditionColumn :: SomeColumn }
    deriving (Generic, Eq, Ord, Show)

type ProjectColSpec = Either (InternalColumn, Mir.DataType ) SomeColumn

data Operator
    = CustomOp { opName :: QualifiedBinding, opInputs :: [Either Mir.DataType SomeColumn] }
    | Join { joinType :: Mir.JoinType, joinOn :: [(SomeColumn, SomeColumn)] }
    | Project { projectEmit :: [ProjectColSpec]}
    | Identity
    | Sink
    | Source Mir.Table
    | Filter { conditions :: HashMap SomeColumn ( Mir.FilterCondition Mir.Column), arguments :: (Binding, [Binding]) }
    | IsEmptyCheck
    | Select SelectPayload
    | Ctrl Int CtrlType
    deriving (Eq, Generic)

instance Show Operator where
    show = toString . quickRender

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


data OperatorDescription
    = Op_MIR (QualifiedBinding, Operator)
    | Op_UDF UDFDescription
    deriving (Eq, Generic, Show)

data UDFDescription = UDFDescription
      { generations :: [GenerationType]
      , udfName :: QualifiedBinding
      , inputBindings :: [Binding]
      , udfState :: Maybe (QualifiedBinding, [Lit])
      , referencedFields :: [Int]
      , execSemantic :: (ExecSem, ExecSem)
      } deriving (Eq, Generic, Show)

type RegisterOperator = OperatorDescription -> IO ()


instance B.Binary GenerationType
instance B.Binary UDFDescription
instance B.Binary Operator
instance B.Binary CtrlType
instance B.Binary OperatorDescription
instance NFData CtrlType
instance NFData Operator
instance Hashable a => Hashable (GScope a)
instance NFData a => NFData (GScope a)
instance Hashable InternalColumn
instance NFData InternalColumn
instance B.Binary InternalColumn
instance B.Binary ExecSem

instance (Eq a, Hashable a, B.Binary a, B.Binary b) => B.Binary (HashMap a b) where
    put = B.put . HashMap.toList
    get = HashMap.fromList <$> B.get
