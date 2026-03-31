import KissingNumber.PSD6Defs
import KissingNumber.TestBBSplit
import KissingNumber.TestBCSplit
import KissingNumber.TestCCSplit
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators RealInnerProductSpace
open Real Finset
open PSD6Defs

noncomputable section

/-!
# PSD Cross-Terms for k=6

Sprint-in-progress:
- shared defs/helpers moved to `PSD6Defs`
- completed deterministic wins: `sum_DD`, `sum_BD`, `sum_CD`
- remaining lemmas are being completed in order
-/

private abbrev T6k := PSD6Defs.T6

private lemma sum_AA (x y : EuclideanSpace ℝ (Fin 8)) :
    ∑ p : T6k, A6 x p * A6 y p =
    (@inner ℝ _ _ x y) ^ 6 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  simp only [A6]
  simp_rw [Fintype.sum_prod_type]
  have hmul : ∀ a b c d e f : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp e * x.ofLp f *
      (y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d * y.ofLp e * y.ofLp f) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) *
      (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) * (x.ofLp f * y.ofLp f) := by
    intro a b c d e f
    ring
  simp_rw [hmul, factor6, ← hs]
  ring

set_option maxHeartbeats 800000000 in
private lemma sum_AB (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) :
    ∑ p : T6k, A6 x p * B6 y p =
    15 * (@inner ℝ _ _ x y) ^ 4 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  simp only [A6, B6]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 200000000 }) only [mul_add, Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, one_mul]
  try simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  try simp_rw (config := { maxSteps := 200000000 }) [sum_ite_prop_zero]
  try simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  try simp_rw (config := { maxSteps := 200000000 }) [sum_ite_prop_zero]
  try simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  try simp_rw (config := { maxSteps := 200000000 }) [sum_ite_prop_zero]
  try simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  try simp_rw (config := { maxSteps := 200000000 }) [sum_ite_prop_zero]
  try simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have r1 : ∀ a b c d e : Fin 8,
      x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp e *
        (y.ofLp b * y.ofLp c * y.ofLp d * y.ofLp e) =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) *
        (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r2 : ∀ a b c d e : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp d * x.ofLp e *
        (y.ofLp b * y.ofLp c * y.ofLp d * y.ofLp e) =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) *
        (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r3 : ∀ a b c d e : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp d * x.ofLp e *
        (y.ofLp b * y.ofLp c * y.ofLp d * y.ofLp e) =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) *
        (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r4 : ∀ a b c d e : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp a * x.ofLp e *
        (y.ofLp b * y.ofLp c * y.ofLp d * y.ofLp e) =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) *
        (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r5 : ∀ a b c d e : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp e * x.ofLp a *
        (y.ofLp b * y.ofLp c * y.ofLp d * y.ofLp e) =
      (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) *
        (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r6 : ∀ a b c d e : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp e *
        (y.ofLp a * y.ofLp c * y.ofLp d * y.ofLp e) =
      (x.ofLp b * x.ofLp b) * (x.ofLp a * y.ofLp a) * (x.ofLp c * y.ofLp c) *
        (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r7 : ∀ a b c d e : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp d * x.ofLp e *
        (y.ofLp a * y.ofLp c * y.ofLp d * y.ofLp e) =
      (x.ofLp b * x.ofLp b) * (x.ofLp a * y.ofLp a) * (x.ofLp c * y.ofLp c) *
        (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r8 : ∀ a b c d e : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp b * x.ofLp e *
        (y.ofLp a * y.ofLp c * y.ofLp d * y.ofLp e) =
      (x.ofLp b * x.ofLp b) * (x.ofLp a * y.ofLp a) * (x.ofLp c * y.ofLp c) *
        (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r9 : ∀ a b c d e : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp e * x.ofLp b *
        (y.ofLp a * y.ofLp c * y.ofLp d * y.ofLp e) =
      (x.ofLp b * x.ofLp b) * (x.ofLp a * y.ofLp a) * (x.ofLp c * y.ofLp c) *
        (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r10 : ∀ a b c d e : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp d * x.ofLp e *
        (y.ofLp a * y.ofLp b * y.ofLp d * y.ofLp e) =
      (x.ofLp c * x.ofLp c) * (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) *
        (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r11 : ∀ a b c d e : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp c * x.ofLp e *
        (y.ofLp a * y.ofLp b * y.ofLp d * y.ofLp e) =
      (x.ofLp c * x.ofLp c) * (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) *
        (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r12 : ∀ a b c d e : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp e * x.ofLp c *
        (y.ofLp a * y.ofLp b * y.ofLp d * y.ofLp e) =
      (x.ofLp c * x.ofLp c) * (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) *
        (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r13 : ∀ a b c d e : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp d * x.ofLp e *
        (y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp e) =
      (x.ofLp d * x.ofLp d) * (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) *
        (x.ofLp c * y.ofLp c) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r14 : ∀ a b c d e : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp e * x.ofLp d *
        (y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp e) =
      (x.ofLp d * x.ofLp d) * (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) *
        (x.ofLp c * y.ofLp c) * (x.ofLp e * y.ofLp e) := by intros; ring
  have r15 : ∀ a b c d e : Fin 8,
      x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp e * x.ofLp e *
        (y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d) =
      (x.ofLp e * x.ofLp e) * (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) *
        (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) := by intros; ring
  have hS2 :
      ∑ x_1, ∑ x_2, ∑ x_3, ∑ x_4, ∑ x_5,
        x.ofLp x_2 * x.ofLp x_2 * (x.ofLp x_1 * y.ofLp x_1) * (x.ofLp x_3 * y.ofLp x_3) *
          (x.ofLp x_4 * y.ofLp x_4) * (x.ofLp x_5 * y.ofLp x_5) = s ^ 4 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c; arg 2; ext d; arg 2; ext e
      rw [show x.ofLp b * x.ofLp b * (x.ofLp a * y.ofLp a) * (x.ofLp c * y.ofLp c) *
          (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) *
          (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) from by ring]
    simp_rw [factor5, hxn, ← hs]
    ring
  have hS3 :
      ∑ x_1, ∑ x_2, ∑ x_3, ∑ x_4, ∑ x_5,
        x.ofLp x_3 * x.ofLp x_3 * (x.ofLp x_1 * y.ofLp x_1) * (x.ofLp x_2 * y.ofLp x_2) *
          (x.ofLp x_4 * y.ofLp x_4) * (x.ofLp x_5 * y.ofLp x_5) = s ^ 4 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c; arg 2; ext d; arg 2; ext e
      rw [show x.ofLp c * x.ofLp c * (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) *
          (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) *
          (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) from by ring]
    simp_rw [factor5, hxn, ← hs]
    ring
  have hS4 :
      ∑ x_1, ∑ x_2, ∑ x_3, ∑ x_4, ∑ x_5,
        x.ofLp x_4 * x.ofLp x_4 * (x.ofLp x_1 * y.ofLp x_1) * (x.ofLp x_2 * y.ofLp x_2) *
          (x.ofLp x_3 * y.ofLp x_3) * (x.ofLp x_5 * y.ofLp x_5) = s ^ 4 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c; arg 2; ext d; arg 2; ext e
      rw [show x.ofLp d * x.ofLp d * (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) *
          (x.ofLp c * y.ofLp c) * (x.ofLp e * y.ofLp e) =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) *
          (x.ofLp d * x.ofLp d) * (x.ofLp e * y.ofLp e) from by ring]
    simp_rw [factor5, hxn, ← hs]
    ring
  have hS5 :
      ∑ x_1, ∑ x_2, ∑ x_3, ∑ x_4, ∑ x_5,
        x.ofLp x_5 * x.ofLp x_5 * (x.ofLp x_1 * y.ofLp x_1) * (x.ofLp x_2 * y.ofLp x_2) *
          (x.ofLp x_3 * y.ofLp x_3) * (x.ofLp x_4 * y.ofLp x_4) = s ^ 4 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c; arg 2; ext d; arg 2; ext e
      rw [show x.ofLp e * x.ofLp e * (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) *
          (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) *
          (x.ofLp d * y.ofLp d) * (x.ofLp e * x.ofLp e) from by ring]
    simp_rw [factor5, hxn, ← hs]
    ring
  simp_rw [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15]
  simp_rw [factor5, hxn, ← hs]
  simp_rw [hS2, hS3, hS4, hS5]
  ring

private lemma sum_BA (x y : EuclideanSpace ℝ (Fin 8)) (hy : ‖y‖ = 1) :
    ∑ p : T6k, B6 x p * A6 y p = 15 * (@inner ℝ _ _ x y) ^ 4 := by
  simp_rw [show ∀ p, B6 x p * A6 y p = A6 y p * B6 x p from fun p => mul_comm _ _]
  rw [sum_AB y x hy, real_inner_comm y x]

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
  have r1 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp d * x.ofLp d * (y.ofLp a * y.ofLp b) = (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r2 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp c * x.ofLp d * (y.ofLp a * y.ofLp b) = (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r3 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp d * x.ofLp c * (y.ofLp a * y.ofLp b) = (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r4 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp d * x.ofLp d * (y.ofLp a * y.ofLp c) = (x.ofLp a * y.ofLp a) * (x.ofLp c * y.ofLp c) * (x.ofLp b * x.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r5 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp b * x.ofLp d * (y.ofLp a * y.ofLp c) = (x.ofLp a * y.ofLp a) * (x.ofLp c * y.ofLp c) * (x.ofLp b * x.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r6 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp d * x.ofLp b * (y.ofLp a * y.ofLp c) = (x.ofLp a * y.ofLp a) * (x.ofLp c * y.ofLp c) * (x.ofLp b * x.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r7 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp d * (y.ofLp a * y.ofLp c) = (x.ofLp a * y.ofLp a) * (x.ofLp c * y.ofLp c) * (x.ofLp b * x.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r8 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp b * x.ofLp c * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r9 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp c * x.ofLp b * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r10 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp c * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r11 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp d * x.ofLp c * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r12 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp d * x.ofLp b * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r13 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp d * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r14 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * x.ofLp c * x.ofLp d * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r15 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp b * x.ofLp d * (y.ofLp a * y.ofLp d) = (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp b * x.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r16 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp d * x.ofLp d * (y.ofLp b * y.ofLp c) = (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r17 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp a * x.ofLp d * (y.ofLp b * y.ofLp c) = (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r18 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp d * x.ofLp a * (y.ofLp b * y.ofLp c) = (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r19 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp d * x.ofLp d * (y.ofLp b * y.ofLp c) = (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r20 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp a * x.ofLp c * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r21 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp c * x.ofLp a * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r22 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp d * x.ofLp c * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r23 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp d * x.ofLp c * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r24 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp d * x.ofLp a * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r25 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp c * x.ofLp d * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r26 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp c * x.ofLp d * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r27 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp a * x.ofLp d * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r28 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp d * (y.ofLp b * y.ofLp c) = (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp d * x.ofLp d) := by intros; ring
  have r29 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp a * x.ofLp b * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r30 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp b * x.ofLp a * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r31 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp c * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have r32 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp d * x.ofLp b * (y.ofLp c * y.ofLp d) = (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r33 : ∀ a b c d : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp d * (y.ofLp b * y.ofLp d) = (x.ofLp b * y.ofLp b) * (x.ofLp d * y.ofLp d) * (x.ofLp a * x.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
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

private lemma sum_CA (x y : EuclideanSpace ℝ (Fin 8)) (hy : ‖y‖ = 1) :
    ∑ p : T6k, C6 x p * A6 y p = 45 * (@inner ℝ _ _ x y) ^ 2 := by
  simp_rw [show ∀ p, C6 x p * A6 y p = A6 y p * C6 x p from fun p => mul_comm _ _]
  rw [sum_AC y x hy, real_inner_comm y x]

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
  simp only [mul_one]
  norm_num

private lemma sum_DA (x y : EuclideanSpace ℝ (Fin 8)) (hy : ‖y‖ = 1) :
    ∑ p : T6k, D6 x p * A6 y p = 15 := by
  simp_rw [show ∀ p, D6 x p * A6 y p = A6 y p * D6 x p from fun p => mul_comm _ _]
  exact sum_AD y x hy

private lemma sum_BB (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, B6 x p * B6 y p =
    240 * (@inner ℝ _ _ x y) ^ 4 + 90 * (@inner ℝ _ _ x y) ^ 2 := by
  have hAA := TestBBSplit.sum_B6a_B6a x y hx hy
  have hAB := TestBBSplit.sum_B6a_B6b x y hx hy
  have hBA :
      ∑ p : T6k, TestBBSplit.B6b x p * TestBBSplit.B6a y p =
      20 * (@inner ℝ _ _ x y) ^ 4 + 30 * (@inner ℝ _ _ x y) ^ 2 := by
    simp_rw [show ∀ p, TestBBSplit.B6b x p * TestBBSplit.B6a y p =
        TestBBSplit.B6a y p * TestBBSplit.B6b x p from fun p => by ring]
    rw [TestBBSplit.sum_B6a_B6b y x hy hx, real_inner_comm y x]
  have hBB := TestBBSplit.sum_B6b_B6b x y hx hy
  calc
    ∑ p : T6k, B6 x p * B6 y p
        = ∑ p : T6k, (TestBBSplit.B6a x p + TestBBSplit.B6b x p) *
            (TestBBSplit.B6a y p + TestBBSplit.B6b y p) := by
          congr 1; ext p
          rw [TestBBSplit.B6_split, TestBBSplit.B6_split]
    _ = (∑ p : T6k, TestBBSplit.B6a x p * TestBBSplit.B6a y p)
        + (∑ p : T6k, TestBBSplit.B6a x p * TestBBSplit.B6b y p)
        + (∑ p : T6k, TestBBSplit.B6b x p * TestBBSplit.B6a y p)
        + (∑ p : T6k, TestBBSplit.B6b x p * TestBBSplit.B6b y p) := by
          simp [mul_add, add_mul, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]
    _ = 240 * (@inner ℝ _ _ x y) ^ 4 + 90 * (@inner ℝ _ _ x y) ^ 2 := by
          rw [hAA, hAB, hBA, hBB]
          ring

private lemma sum_BC (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, B6 x p * C6 y p =
    1260 * (@inner ℝ _ _ x y) ^ 2 + 45 := by
  have hAA := TestBCSplit.sum_B6a_C6a x y hx hy
  have hAB := TestBCSplit.sum_B6a_C6b x y hx hy
  have hBA := TestBCSplit.sum_B6b_C6a x y hx hy
  have hBB := TestBCSplit.sum_B6b_C6b x y hx hy
  calc
    ∑ p : T6k, B6 x p * C6 y p
        = ∑ p : T6k, (TestBBSplit.B6a x p + TestBBSplit.B6b x p) *
            (TestBCSplit.C6a y p + TestBCSplit.C6b y p) := by
          congr 1; ext p
          rw [TestBBSplit.B6_split, TestBCSplit.C6_split]
    _ = (∑ p : T6k, TestBBSplit.B6a x p * TestBCSplit.C6a y p)
        + (∑ p : T6k, TestBBSplit.B6a x p * TestBCSplit.C6b y p)
        + (∑ p : T6k, TestBBSplit.B6b x p * TestBCSplit.C6a y p)
        + (∑ p : T6k, TestBBSplit.B6b x p * TestBCSplit.C6b y p) := by
          simp [mul_add, add_mul, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]
    _ = 1260 * (@inner ℝ _ _ x y) ^ 2 + 45 := by
          rw [hAA, hAB, hBA, hBB]
          ring

private lemma sum_CB (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, C6 x p * B6 y p =
    1260 * (@inner ℝ _ _ x y) ^ 2 + 45 := by
  simp_rw [show ∀ p, C6 x p * B6 y p = B6 y p * C6 x p from fun p => mul_comm _ _]
  rw [sum_BC y x hy hx, real_inner_comm y x]

set_option maxHeartbeats 800000000 in
private lemma sum_BD (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, B6 x p * D6 y p =
    (540 : ℝ) := by
  have hxn := ofLp_norm_sq x hx
  simp only [B6, D6]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 200000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 200000000 }) only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul, one_mul]
  simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 200000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  try simp_rw (config := { maxSteps := 200000000 }) [sum_ite_prop_zero]
  try simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  try simp_rw (config := { maxSteps := 200000000 }) [sum_ite_prop_zero]
  try simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  try simp_rw (config := { maxSteps := 200000000 }) [sum_ite_prop_zero]
  try simp (config := { maxSteps := 200000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have r1 : ∀ a b : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp b = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r2 : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp b = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r3 : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp a = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have r4 : ∀ a b : Fin 8, x.ofLp b * x.ofLp b * (x.ofLp a * x.ofLp a) = (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  simp_rw [r1, r2, r3, r4, ← Finset.mul_sum, hxn]
  norm_num

private lemma sum_DB (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, D6 x p * B6 y p =
    (540 : ℝ) := by
  simp_rw [show ∀ p, D6 x p * B6 y p = B6 y p * D6 x p from fun p => mul_comm _ _]
  exact sum_BD y x hy hx

private lemma sum_CC (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, C6 x p * C6 y p =
    7560 * (@inner ℝ _ _ x y) ^ 2 + 1080 := by
  have hAA := TestCCSplit.sum_C6a_C6a x y hx hy
  have hAB := TestCCSplit.sum_C6a_C6b x y hx hy
  have hBA := TestCCSplit.sum_C6b_C6a x y hx hy
  have hBB := TestCCSplit.sum_C6b_C6b x y hx hy
  calc
    ∑ p : T6k, C6 x p * C6 y p
        = ∑ p : T6k, (TestBCSplit.C6a x p + TestBCSplit.C6b x p) *
            (TestBCSplit.C6a y p + TestBCSplit.C6b y p) := by
          congr 1; ext p
          rw [TestBCSplit.C6_split, TestBCSplit.C6_split]
    _ = (∑ p : T6k, TestBCSplit.C6a x p * TestBCSplit.C6a y p)
        + (∑ p : T6k, TestBCSplit.C6a x p * TestBCSplit.C6b y p)
        + (∑ p : T6k, TestBCSplit.C6b x p * TestBCSplit.C6a y p)
        + (∑ p : T6k, TestBCSplit.C6b x p * TestBCSplit.C6b y p) := by
          simp [mul_add, add_mul, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]
    _ = 7560 * (@inner ℝ _ _ x y) ^ 2 + 1080 := by
          rw [hAA, hAB, hBA, hBB]
          ring

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

private lemma sum_DC (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, D6 x p * C6 y p =
    (5400 : ℝ) := by
  simp_rw [show ∀ p, D6 x p * C6 y p = C6 y p * D6 x p from fun p => mul_comm _ _]
  exact sum_CD y x hy hx

set_option maxHeartbeats 400000000 in
private lemma sum_DD (x y : EuclideanSpace ℝ (Fin 8)) :
    ∑ p : T6k, D6 x p * D6 y p = 14400 := by
  simp only [D6]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 100000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 100000000 }) only [mul_ite, mul_zero, mul_one]
  simp (config := { maxSteps := 100000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 100000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 100000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 100000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 100000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  norm_num

private lemma phi6_kernel (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, phi6 x p * phi6 y p =
    (231 : ℝ) / 896 * P8 6 (@inner ℝ _ _ x y) := by
  suffices h : ∑ p : T6k, phi6 x p * phi6 y p =
      (@inner ℝ _ _ x y) ^ 6 - 15 / 16 * (@inner ℝ _ _ x y) ^ 4
      + 45 / 224 * (@inner ℝ _ _ x y) ^ 2 - 5 / 896 by
    rw [h, P8_6]
    ring
  simp_rw [phi6_product]
  simp only [sub_eq_add_neg]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  rw [sum_AA, sum_AB x y hx, sum_BA x y hy, sum_AC x y hx, sum_CA x y hy,
      sum_AD x y hx, sum_DA x y hy,
      sum_BB x y hx hy, sum_BC x y hx hy, sum_CB x y hx hy,
      sum_BD x y hx hy, sum_DB x y hx hy,
      sum_CC x y hx hy, sum_CD x y hx hy, sum_DC x y hx hy,
      sum_DD]
  ring

def phi6Feature (x : EuclideanSpace ℝ (Fin 8)) (p : T6k) : ℝ :=
  phi6 x p

lemma phi6Feature_kernel (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, phi6Feature x p * phi6Feature y p =
    (231 : ℝ) / 896 * P8 6 (@inner ℝ _ _ x y) := by
  simp only [phi6Feature]
  exact phi6_kernel x y hx hy

end
