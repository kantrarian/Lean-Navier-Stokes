import Lake
open Lake DSL

package «HPDE_common» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «HPDE_common» where
  -- add library configuration options here
