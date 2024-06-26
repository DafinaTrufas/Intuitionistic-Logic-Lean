import Lake
open Lake DSL

package IL {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib IL {
  -- add library configuration options here
}
