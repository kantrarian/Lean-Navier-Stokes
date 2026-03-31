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

set_option maxHeartbeats 800000000 in
private lemma sum_AD (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) :
    ∑ p : T6k, A6 x p * D6 y p = 15 := by
  have hxn := ofLp_norm_sq x hx
  simp only [A6, D6]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 200000000 }) only [mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 200000000 }) only [mul_ite, mul_zero, mul_one]
  simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 200000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 200000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have r1 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp c =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r2 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r3 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp b * x.ofLp c =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r4 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp c =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r5 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp b =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r6 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp b * x.ofLp c =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r7 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp c * x.ofLp b =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r8 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp c =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r9 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp c =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r10 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp a =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r11 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp c * x.ofLp b =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r12 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp a * x.ofLp c =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r13 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp c * x.ofLp a =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r14 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp a * x.ofLp b =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r15 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp b * x.ofLp a =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  simp_rw [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, factor3, hxn]
  -- Try different closers:
  simp only [mul_one, one_mul]
  norm_num

end
