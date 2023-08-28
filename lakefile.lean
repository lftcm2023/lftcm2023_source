import Lake
open Lake DSL

package lftcm2023 {
  -- add package configuration options here
}

@[default_target]
lean_lib MIL {
  -- add library configuration options here
}

@[default_target]
lean_lib CIL {
  -- add library configuration options here
}

@[default_target]
lean_lib Projects {
  -- add library configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"
