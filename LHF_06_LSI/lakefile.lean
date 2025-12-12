import Lake
open Lake DSL

package LHF_06_LSI where
  version := v!"0.1.0"

-- Depend on HPDE-03 for Gaussian LSI infrastructure
require HPDE_03_logsob from "../HPDE_03_logsob"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib LHF_06_LSI where
  -- Bakry-Émery implies Log-Sobolev
  -- Now wired to HPDE-03 proven Gaussian LSI infrastructure
