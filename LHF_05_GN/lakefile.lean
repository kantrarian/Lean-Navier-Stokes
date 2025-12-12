import Lake
open Lake DSL

package LHF_05_GN where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib LHF_05_GN where
  -- Gagliardo-Nirenberg interpolation for GKT
