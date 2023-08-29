import Lake
open Lake DSL

def moreServerArgs := #[
  "-Dpp.unicode.fun=true", -- pretty-prints `fun a ↦ b`
  -- this is set in mathlib, but the exercises are nicer to read without it
  -- "-DautoImplicit=false",
  "-DrelaxedAutoImplicit=false"
]

-- These settings only apply during `lake build`, but not in VSCode editor.
def moreLeanArgs := moreServerArgs

package lftcm2023 where
  moreServerArgs := moreServerArgs

@[default_target]
lean_lib MIL where
  moreLeanArgs := moreLeanArgs

@[default_target]
lean_lib CIL {
  -- add library configuration options here
}

@[default_target]
lean_lib Projects {
  -- add library configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"
