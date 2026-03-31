import Mathlib.Analysis.InnerProductSpace.PiL2
open scoped BigOperators

set_option maxHeartbeats 400000 in
example (s : ℝ) (x y : EuclideanSpace ℝ (Fin 8))
    (hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a) :
    ∑ a : Fin 8, s * x.ofLp a * y.ofLp a = s ^ 2 := by
  have rs : ∀ a : Fin 8, s * x.ofLp a * y.ofLp a = s * (x.ofLp a * y.ofLp a) := by intros; ring
  simp_rw [rs, ← Finset.mul_sum, ← hs]; ring
