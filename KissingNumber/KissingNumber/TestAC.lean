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
private lemma sum_AC (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) :
    ∑ p : T6k, A6 x p * C6 y p =
    45 * (@inner ℝ _ _ x y) ^ 2 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  simp only [A6, C6]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 30000000 }) only [mul_add, Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, mul_one]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [sum_ite_prop_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [sum_ite_prop_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [sq]
  -- Rearrangement lemmas: normalize products for factor4
  -- Group 1: y-pair = (a,b), squared = (c,d) → positions match factor4 directly
  have r1 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp d * x.ofLp d * (y.ofLp a * y.ofLp b) = (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r2 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp c * x.ofLp d * (y.ofLp a * y.ofLp b) = (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r3 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp d * x.ofLp c * (y.ofLp a * y.ofLp b) = (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) * (x.ofLp d * x.ofLp d) := by intros; ring
  -- Group 2: y-pair = (a,c), squared = (b,d) → use factor4_acbd
  have r4 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp d * x.ofLp d * (y.ofLp a * y.ofLp c) = (x.ofLp a * y.ofLp a) * (x.ofLp c * y.ofLp c) * (x.ofLp b * x.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r5 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp b * x.ofLp d * (y.ofLp a * y.ofLp c) = (x.ofLp a * y.ofLp a) * (x.ofLp c * y.ofLp c) * (x.ofLp b * x.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r6 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp d * x.ofLp b * (y.ofLp a * y.ofLp c) = (x.ofLp a * y.ofLp a) * (x.ofLp c * y.ofLp c) * (x.ofLp b * x.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r7 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp d * (y.ofLp a * y.ofLp c) = (x.ofLp a * y.ofLp a) * (x.ofLp c * y.ofLp c) * (x.ofLp b * x.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  -- Group 3: y-pair = (a,d), squared = (b,c) → use factor4_adbc
  have r8 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp b * x.ofLp c * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r9 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp c * x.ofLp b * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r10 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp c * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r11 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp d * x.ofLp c * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r12 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp d * x.ofLp b * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r13 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp d * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r14 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp c * x.ofLp d * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r15 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp b * x.ofLp d * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  -- Group 4: y-pair = (b,c), squared = (a,d) → use factor4_bcad
  have r16 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp d * x.ofLp d * (y.ofLp b * y.ofLp c) = (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r17 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp a * x.ofLp d * (y.ofLp b * y.ofLp c) = (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r18 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp d * x.ofLp a * (y.ofLp b * y.ofLp c) = (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r19 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp d * x.ofLp d * (y.ofLp b * y.ofLp c) = (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r28 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp d * (y.ofLp b * y.ofLp c) = (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp d * x.ofLp d) := by intros; ring
  -- Group 5: y-pair = (b,d), squared = (a,c) → use factor4_bdac
  have r20 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp a * x.ofLp c * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r21 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp c * x.ofLp a * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r22 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp d * x.ofLp c * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r23 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp d * x.ofLp c * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r24 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp d * x.ofLp a * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r25 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp c * x.ofLp d * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r26 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp c * x.ofLp d * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r27 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp a * x.ofLp d * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r31 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp c * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r33 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp d * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  -- Group 6: y-pair = (c,d), squared = (a,b) → use factor4_cdab
  have r29 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp a * x.ofLp b * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r30 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp b * x.ofLp a * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r32 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp d * x.ofLp b * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r34 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp b * x.ofLp d * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r35 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp d * x.ofLp a * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r36 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp b * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r37 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp d * x.ofLp b * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r38 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp b * x.ofLp d * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r39 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp a * x.ofLp d * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r40 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp d * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r41 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp d * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  -- NEW: Missing r-rules for patterns where both squared pairs in positions 1-4
  have r42 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp d * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r43 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r44 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp d * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r45 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp a * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  -- Apply r-rules + factor4 variants + hxn/hs
  simp_rw [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15,
           r16, r17, r18, r19, r28,
           r20, r21, r22, r23, r24, r25, r26, r27, r31, r33,
           r29, r30, r32, r34, r35, r36, r37, r38, r39, r40, r41,
           r42, r43, r44, r45,
           factor4, factor4_acbd, factor4_adbc, factor4_bcad, factor4_bdac, factor4_cdab,
           hxn, ← hs]
  simp only [mul_one, one_mul]
  ring

end
