import Lake
open Lake DSL

package «lean-example» where
  -- add package configuration options here

lean_lib «LeanExample» where
  -- add library configuration options here

@[default_target]
lean_exe «lean-example» where
  root := `Main
