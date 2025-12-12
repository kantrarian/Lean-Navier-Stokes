import Lake
open Lake DSL

package HPDE_04_campanato where
  -- Package settings

require HPDE_common from "../HPDE_common"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib HPDE_04_campanato where
  -- Library settings
