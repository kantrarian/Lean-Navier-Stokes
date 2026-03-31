import KissingNumber.PSD6Defs
import KissingNumber.TestBBSplit
import KissingNumber.TestBCSplit
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators RealInnerProductSpace
open Real Finset
open PSD6Defs TestBCSplit

noncomputable section

set_option maxHeartbeats 4000000000 in
lemma test_B6a_C6b (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : PSD6Defs.T6, TestBBSplit.B6a x p * TestBCSplit.C6b y p =
    360 * (@inner ℝ _ _ x y) ^ 2 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [TestBBSplit.B6a, C6b]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 800000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 800000000 }) only [mul_ite, mul_zero, ite_mul, zero_mul, one_mul]
  simp (config := { maxSteps := 800000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 800000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 800000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 800000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 800000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [mul_one]
  ring_nf
  trace_state
  sorry
