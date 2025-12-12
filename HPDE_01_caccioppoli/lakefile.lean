import Lake
open Lake DSL

package «HPDE_01_caccioppoli» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

require HPDE_common from "../HPDE_common"

@[default_target]
lean_lib «HPDE_01_caccioppoli» where
  -- add library configuration options here
