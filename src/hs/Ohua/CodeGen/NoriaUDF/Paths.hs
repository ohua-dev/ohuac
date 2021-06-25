module Ohua.CodeGen.NoriaUDF.Paths where

import Ohua.Prelude

type Path = forall s . (IsString s, Monoid s) => s

serverDir :: Path
serverDir =
    -- "server" -- for version 0.7
    "noria-server" -- for version 0.1.2


mirSourceDir :: Path
mirSourceDir = serverDir <> "/mir/src"

serverSourceDir :: Path
serverSourceDir = serverDir <> "/src"

dataflowSourceDir :: Path
dataflowSourceDir = serverDir <> "/dataflow/src"

udfsDir :: Path
udfsDir = mirSourceDir <> "/udfs"

udfsModFile :: Path
udfsModFile = udfsDir <> "/mod.rs"

dfOpsDir :: Path
dfOpsDir = dataflowSourceDir <> "/ops"

dfOpsFile :: Path
dfOpsFile = dfOpsDir <> "/mod.rs"

opsInterfaceFile :: Path
opsInterfaceFile = dfOpsDir <> "/ohua/att3.rs"

schemaFile :: Path
schemaFile = serverSourceDir <> "/controller/schema.rs"

generatedOpsModFile :: Path
generatedOpsModFile =
    dataflowSourceDir <> "/ops/ohua/generated/mod.rs"

generatedStatesModFile :: Path
generatedStatesModFile =
    dataflowSourceDir <> "/state/ohua/generated/mod.rs"
