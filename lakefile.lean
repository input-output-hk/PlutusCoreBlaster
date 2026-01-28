import Lake
open Lake DSL

package «PlutusCore» where
  -- add package configuration options here

@[default_target]
lean_lib «PlutusCore» where
  -- add library configuration options here

@[test_driver]
lean_lib «Tests» where
  -- add library configuration options here

lean_lib «Lemmas» where
  -- add library configuration options here
