import Lake
open Lake DSL

package «PlutusCore» where
  -- add package configuration options here
  -- `fix-abbrev-in-codomain` (Lean-blaster#193) rather than `main`: it carries the
  -- `abbrev`-in-codomain fix that the BLS builtins' return types need. Move back to
  -- `main` once that PR merges.
  require Blaster from git "https://github.com/input-output-hk/Lean-blaster" @ "fix-abbrev-in-codomain"

@[default_target]
lean_lib «PlutusCore» where
  -- add library configuration options here

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
