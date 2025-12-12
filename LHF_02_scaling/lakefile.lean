import Lake
open Lake DSL

package LHF_02_scaling where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib LHF_02_scaling where
  -- GKT functional scaling invariance
