import Lake
open Lake DSL

package «PlutusCore» where
  -- add package configuration options here
  require Blaster from "../Lean-blaster"

input_file assuranceSchema where
  path := "PlutusCore/UPLC/BlueprintEncoding/assurance.schema.json"
  text := true

input_file assuranceV2 where
  path := "PlutusCore/UPLC/BlueprintEncoding/assurance-v2.schema.json"
  text := true

input_file checkingContext where
  path := "PlutusCore/UPLC/BlueprintEncoding/checking-context.schema.json"
  text := true

input_file interfaceBlueprint where
  path := "PlutusCore/UPLC/BlueprintEncoding/interface.schema.json"
  text := true

input_file interfaceValue where
  path := "PlutusCore/UPLC/BlueprintEncoding/value.schema.json"
  text := true

input_file baseBlueprint where
  path := "PlutusCore/UPLC/BlueprintEncoding/blueprint.schema.json"
  text := true

@[default_target]
lean_lib «PlutusCore» where
  precompileModules := true
  moreLeancArgs := #["-O3"]
  needs := #[assuranceSchema, assuranceV2, checkingContext, interfaceBlueprint, interfaceValue, baseBlueprint]

@[test_driver]
lean_lib «Tests» where
  -- add library configuration options here

lean_lib «Lemmas» where
  -- add library configuration options here

lean_lib «Cryptograph» where
  -- add library configuration options here

lean_exe «gen_conformance_tests» where
  srcDir := "scripts"
  root := `GenConformanceTests

-- `#prep_uplc` benchmark harness (see Benchmark/README.md).
-- Must not be precompiled: its generated cases import
-- `PlutusCore.UPLC.ScriptEncoding.Tests`, whose native code would then have to be built.
lean_lib «Benchmark»

lean_exe «bench_prep_uplc» where
  root := `Benchmark.PrepUplc.Driver.Main
