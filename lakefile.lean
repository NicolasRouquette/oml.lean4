import Lake
import Lake.DSL
open System Lake DSL

require std4 from git "https://github.com/leanprover/std4.git"

package «oml» where
  -- add package configuration options here
  srcDir := "src"

lean_lib «Oml» where
  -- add library configuration options here

@[default_target]
lean_exe «oml» where
  root := `Main
  supportInterpreter := true
