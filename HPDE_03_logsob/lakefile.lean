import Lake
open Lake DSL

package HPDE_03_logsob where
  -- Package settings

require HPDE_common from "../HPDE_common"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib HPDE_03_logsob where
  -- Library settings
