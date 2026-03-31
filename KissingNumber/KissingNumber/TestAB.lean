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

set_option maxHeartbeats 400000000 in
example (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) :
    ∑ p : T6k, A6 x p * B6 y p =
    15 * (@inner ℝ _ _ x y) ^ 4 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  simp only [A6, B6]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 200000000 }) only [mul_add, Finset.sum_add_distrib]
  try simp only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul, one_mul]
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
  simp_rw [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, factor5, hxn, ← hs]
  have t2 : ∀ a b c d e : Fin 8,
      x.ofLp b ^ 2 * x.ofLp a * y.ofLp a * x.ofLp c * y.ofLp c * x.ofLp d * y.ofLp d * x.ofLp e * y.ofLp e =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) *
        (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have t3 : ∀ a b c d e : Fin 8,
      x.ofLp c ^ 2 * x.ofLp a * y.ofLp a * x.ofLp b * y.ofLp b * x.ofLp d * y.ofLp d * x.ofLp e * y.ofLp e =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) *
        (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have t4 : ∀ a b c d e : Fin 8,
      x.ofLp d ^ 2 * x.ofLp a * y.ofLp a * x.ofLp b * y.ofLp b * x.ofLp c * y.ofLp c * x.ofLp e * y.ofLp e =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) *
        (x.ofLp d * x.ofLp d) * (x.ofLp e * y.ofLp e) := by intros; ring
  have t5 : ∀ a b c d e : Fin 8,
      x.ofLp e ^ 2 * x.ofLp a * y.ofLp a * x.ofLp b * y.ofLp b * x.ofLp c * y.ofLp c * x.ofLp d * y.ofLp d =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) *
        (x.ofLp d * y.ofLp d) * (x.ofLp e * x.ofLp e) := by intros; ring
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
  simp_rw [hS2, hS3, hS4, hS5]
  ring
