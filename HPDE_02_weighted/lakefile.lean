import Lake
open Lake DSL

package HPDE_02_weighted where
  -- Package settings

require HPDE_common from "../HPDE_common"
require HPDE_01_caccioppoli from "../HPDE_01_caccioppoli"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib HPDE_02_weighted where
  -- Library settings
