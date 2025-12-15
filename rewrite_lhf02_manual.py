from pathlib import Path

out = r"""import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace LHF_02_manual

/-- Scaling predicate for the GKT functional. -/
def satisfies_gkt_scaling (A_omega : Real -> Real) : Prop :=
  forall r I : Real, r > 0 -> I > 0 -> A_omega (I * r) = I^4 * A_omega r

/-- Dimensional-analysis sanity check: the scaling exponent for (p,q)=(2,3) is 4. -/
theorem gkt_dimensional_scaling : ((2:Real)/3) * (3 + 6) / 2 + (2:Real)/2 = 4 := by
  norm_num

/-- Quartic power laws satisfy the scaling law. -/
theorem quartic_power_law_scaling (C : Real) :
  satisfies_gkt_scaling (fun r => C * r^(4:Nat)) := by
  intro r I hr hI
  -- (I*r)^4 = I^4 * r^4
  simp [satisfies_gkt_scaling, mul_pow, mul_assoc, mul_left_comm, mul_comm]
  ring

/-- Existence of a functional with the correct scaling behavior. -/
theorem gkt_scaling_law : Exists (fun A_omega : Real -> Real => satisfies_gkt_scaling A_omega) := by
  refine âŸ¨fun r => r^(4:Nat), ?_âŸ©
  intro r I hr hI
  simp [satisfies_gkt_scaling, mul_pow, mul_assoc, mul_left_comm, mul_comm]
  ring

/-- Critical exponent is zero for (p,q)=(2,3). -/
theorem critical_exponent_is_zero : (2:Real) - 2/(2:Real) - 3/(3:Real) = 0 := by
  norm_num

end LHF_02_manual
"""

p = Path(r"C:\v2_files\lean_proofs\LHF_02_scaling\LHF_02_scaling\LHF_02_manual.lean")
p.write_text(out, encoding="utf-8")
print("rewrote", p)