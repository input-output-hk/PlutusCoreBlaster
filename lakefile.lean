import Lake
open Lake DSL

package «PlutusCore» where
  -- add package configuration options here
  require Blaster from git "https://github.com/input-output-hk/Lean-blaster" @ "beta-lambda-cache-optimization"

@[default_target]
lean_lib «PlutusCore» where
  precompileModules := true
  moreLeancArgs := #["-O3"]

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
