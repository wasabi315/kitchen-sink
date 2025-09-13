import Lake
open Lake DSL

package «free» where
  -- add package configuration options here

lean_lib «Free» where
  -- add library configuration options here

@[default_target]
lean_exe «free» where
  root := `Main
