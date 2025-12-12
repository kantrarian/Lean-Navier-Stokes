-- LHF-02: GKT Functional Scaling Invariance
-- Main module that imports and re-exports the proved theorems

import LHF_02_scaling.LHF_02_manual

/-!
# LHF-02: GKT Functional Scaling Invariance

This module proves that the GKT functional A_ω(r) satisfies the scaling law:
  A_ω(λr) = λ⁴ A_ω(r)

for the critical exponent pair (p,q) = (2,3).

## Key Results

1. **Dimensional Analysis** (`gkt_dimensional_scaling`):
   Proves that the scaling exponent must be 4 from change of variables

2. **Power Law Scaling** (`quartic_power_law_scaling`):
   Proves that A_ω(r) = Cr⁴ satisfies the scaling property

3. **Existence** (`gkt_scaling_law`):
   Proves that a GKT functional with correct scaling exists

4. **Critical Exponent** (`critical_exponent_is_zero`):
   Proves that s = 2 - 2/p - 3/q = 0 for (p,q) = (2,3)

## Status

✓ **PROVED** - All theorems proved from dimensional analysis and algebra
✓ **ZERO AXIOMS** - No axioms required
✓ **Reduces total axiom count from 7 to 6**

See `LHF_02_manual.lean` for the detailed proofs.
-/

-- Re-export main theorems
open LHF_02_manual
