import Lake
open Lake DSL

package «CutsHeineBorel» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib «CutsHeineBorel» {
  -- add library configuration options here
}
