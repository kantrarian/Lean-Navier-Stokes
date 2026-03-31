import KissingNumber.PSD6Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators RealInnerProductSpace
open Real Finset
open PSD6Defs

noncomputable section

private abbrev T6k := PSD6Defs.T6

set_option maxHeartbeats 1600000000 in
private lemma sum_CD (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, C6 x p * D6 y p =
    (5400 : ℝ) := by
  have hxn := ofLp_norm_sq x hx
  simp only [C6, D6]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 400000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 400000000 }) only [mul_ite, mul_zero, mul_one]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  try simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  try simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  try simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  try simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  try simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  try simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [hxn]
  simp only [mul_one]
  norm_num

end
