import Lake
open Lake DSL

package LHF_07_campanato where
  version := v!"0.1.0"

-- Depend on HPDE-04 for Campanato infrastructure
require HPDE_04_campanato from "../HPDE_04_campanato"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib LHF_07_campanato where
  -- Campanato embedding to Hölder regularity
  -- Now wired to HPDE-04 proven infrastructure
