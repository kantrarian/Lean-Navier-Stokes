import Lake
open Lake DSL

package LHF_03_gaussian where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib LHF_03_gaussian where
  -- Add library configuration here
