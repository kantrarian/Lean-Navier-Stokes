import KissingNumber.PSD6Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators RealInnerProductSpace
open Real Finset
open PSD6Defs

noncomputable section

namespace TestBBSplit

private abbrev T6k := PSD6Defs.T6

def B6a (x : EuclideanSpace ℝ (Fin 8)) (p : T6k) : ℝ :=
  let a := p.1; let b := p.2.1; let c := p.2.2.1
  let d := p.2.2.2.1; let e := p.2.2.2.2.1; let f := p.2.2.2.2.2
  (if a = b then 1 else 0) * x c * x d * x e * x f
  + (if a = c then 1 else 0) * x b * x d * x e * x f
  + (if a = d then 1 else 0) * x b * x c * x e * x f
  + (if a = e then 1 else 0) * x b * x c * x d * x f
  + (if a = f then 1 else 0) * x b * x c * x d * x e

def B6b (x : EuclideanSpace ℝ (Fin 8)) (p : T6k) : ℝ :=
  let a := p.1; let b := p.2.1; let c := p.2.2.1
  let d := p.2.2.2.1; let e := p.2.2.2.2.1; let f := p.2.2.2.2.2
  (if b = c then 1 else 0) * x a * x d * x e * x f
  + (if b = d then 1 else 0) * x a * x c * x e * x f
  + (if b = e then 1 else 0) * x a * x c * x d * x f
  + (if b = f then 1 else 0) * x a * x c * x d * x e
  + (if c = d then 1 else 0) * x a * x b * x e * x f
  + (if c = e then 1 else 0) * x a * x b * x d * x f
  + (if c = f then 1 else 0) * x a * x b * x d * x e
  + (if d = e then 1 else 0) * x a * x b * x c * x f
  + (if d = f then 1 else 0) * x a * x b * x c * x e
  + (if e = f then 1 else 0) * x a * x b * x c * x d

lemma B6_split (x : EuclideanSpace ℝ (Fin 8)) (p : T6k) :
    B6 x p = B6a x p + B6b x p := by
  simp only [B6, B6a, B6b]
  ring

set_option maxHeartbeats 1200000000 in
lemma sum_B6a_B6a (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, B6a x p * B6a y p = 60 * (@inner ℝ _ _ x y) ^ 4 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [B6a]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 500000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 500000000 }) only [mul_ite, mul_zero, ite_mul, zero_mul, one_mul]
  simp (config := { maxSteps := 500000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 500000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 500000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 500000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 500000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have t0 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8, ∑ x_5 : Fin 8,
      x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_5 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4 * y.ofLp x_5 =
      8 * s ^ 4 := by
    have rr : ∀ b c d e : Fin 8,
        x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp e * y.ofLp b * y.ofLp c * y.ofLp d * y.ofLp e =
        (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) := by
      intros; ring
    simp_rw [rr]
    simp [Finset.sum_const, Fintype.card_fin]
    simp_rw [factor4, ← hs]
    ring
  have t1 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * y.ofLp x_1 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4 = s ^ 4 := by
    have rr : ∀ a b c d : Fin 8,
        x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) := by
      intros; ring
    simp_rw [rr, factor4, ← hs]
    ring
  have t2 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * y.ofLp x_2 * y.ofLp x_1 * y.ofLp x_3 * y.ofLp x_4 = s ^ 4 := by
    have rr : ∀ a b c d : Fin 8,
        x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * y.ofLp b * y.ofLp a * y.ofLp c * y.ofLp d =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) := by
      intros; ring
    simp_rw [rr, factor4, ← hs]
    ring
  have t3 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_1 * y.ofLp x_4 = s ^ 4 := by
    have rr : ∀ a b c d : Fin 8,
        x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * y.ofLp b * y.ofLp c * y.ofLp a * y.ofLp d =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) := by
      intros; ring
    simp_rw [rr, factor4, ← hs]
    ring
  have t4 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4 * y.ofLp x_1 = s ^ 4 := by
    have rr : ∀ a b c d : Fin 8,
        x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * y.ofLp b * y.ofLp c * y.ofLp d * y.ofLp a =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) := by
      intros; ring
    simp_rw [rr, factor4, ← hs]
    ring
  have t5 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_4 * y.ofLp x_2 * y.ofLp x_1 * y.ofLp x_3 * y.ofLp x_4 = s ^ 4 := by
    have rr : ∀ a b c d : Fin 8,
        x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp d * y.ofLp b * y.ofLp a * y.ofLp c * y.ofLp d =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) := by
      intros; ring
    simp_rw [rr, factor4, ← hs]
    ring
  have t6 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_4 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_1 * y.ofLp x_4 = s ^ 4 := by
    have rr : ∀ a b c d : Fin 8,
        x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp d * y.ofLp b * y.ofLp c * y.ofLp a * y.ofLp d =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) := by
      intros; ring
    simp_rw [rr, factor4, ← hs]
    ring
  have t7 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_4 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4 * y.ofLp x_1 = s ^ 4 := by
    have rr : ∀ a b c d : Fin 8,
        x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp d * y.ofLp b * y.ofLp c * y.ofLp d * y.ofLp a =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) := by
      intros; ring
    simp_rw [rr, factor4, ← hs]
    ring
  have t8 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_4 * y.ofLp x_1 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4 = s ^ 4 := by
    have rr : ∀ a b c d : Fin 8,
        x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp d * y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) := by
      intros; ring
    simp_rw [rr, factor4, ← hs]
    ring
  have t9 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_1 * x.ofLp x_4 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_1 * y.ofLp x_4 = s ^ 4 := by
    have rr : ∀ a b c d : Fin 8,
        x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp d * y.ofLp b * y.ofLp c * y.ofLp a * y.ofLp d =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) := by
      intros; ring
    simp_rw [rr, factor4, ← hs]
    ring
  have t10 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_1 * x.ofLp x_4 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4 * y.ofLp x_1 = s ^ 4 := by
    have rr : ∀ a b c d : Fin 8,
        x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp d * y.ofLp b * y.ofLp c * y.ofLp d * y.ofLp a =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) := by
      intros; ring
    simp_rw [rr, factor4, ← hs]
    ring
  have t11 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_1 * x.ofLp x_4 * y.ofLp x_1 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4 = s ^ 4 := by
    have rr : ∀ a b c d : Fin 8,
        x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp d * y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) := by
      intros; ring
    simp_rw [rr, factor4, ← hs]
    ring
  have t12 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_1 * x.ofLp x_4 * y.ofLp x_2 * y.ofLp x_1 * y.ofLp x_3 * y.ofLp x_4 = s ^ 4 := by
    have rr : ∀ a b c d : Fin 8,
        x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp d * y.ofLp b * y.ofLp a * y.ofLp c * y.ofLp d =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) := by
      intros; ring
    simp_rw [rr, factor4, ← hs]
    ring
  have t13 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_1 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4 * y.ofLp x_1 = s ^ 4 := by
    have rr : ∀ a b c d : Fin 8,
        x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d * y.ofLp a =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) := by
      intros; ring
    simp_rw [rr, factor4, ← hs]
    ring
  have t14 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_1 * y.ofLp x_1 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4 = s ^ 4 := by
    have rr : ∀ a b c d : Fin 8,
        x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp a * y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) := by
      intros; ring
    simp_rw [rr, factor4, ← hs]
    ring
  have t15 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_1 * y.ofLp x_2 * y.ofLp x_1 * y.ofLp x_3 * y.ofLp x_4 = s ^ 4 := by
    have rr : ∀ a b c d : Fin 8,
        x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp a * y.ofLp b * y.ofLp a * y.ofLp c * y.ofLp d =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) := by
      intros; ring
    simp_rw [rr, factor4, ← hs]
    ring
  have t16 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_1 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_1 * y.ofLp x_4 = s ^ 4 := by
    have rr : ∀ a b c d : Fin 8,
        x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp a * y.ofLp b * y.ofLp c * y.ofLp a * y.ofLp d =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) := by
      intros; ring
    simp_rw [rr, factor4, ← hs]
    ring
  have tp0 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8, ∑ x_5 : Fin 8,
      x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_5 * (y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4 * y.ofLp x_5) =
      8 * s ^ 4 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using t0
  have tp1 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * (y.ofLp x_1 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4) = s ^ 4 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using t1
  have tp2 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * (y.ofLp x_2 * y.ofLp x_1 * y.ofLp x_3 * y.ofLp x_4) = s ^ 4 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using t2
  have tp3 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * (y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_1 * y.ofLp x_4) = s ^ 4 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using t3
  have tp4 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * (y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4 * y.ofLp x_1) = s ^ 4 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using t4
  have tp5 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_4 * (y.ofLp x_2 * y.ofLp x_1 * y.ofLp x_3 * y.ofLp x_4) = s ^ 4 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using t5
  have tp6 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_4 * (y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_1 * y.ofLp x_4) = s ^ 4 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using t6
  have tp7 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_4 * (y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4 * y.ofLp x_1) = s ^ 4 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using t7
  have tp8 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_4 * (y.ofLp x_1 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4) = s ^ 4 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using t8
  have tp9 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_1 * x.ofLp x_4 * (y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_1 * y.ofLp x_4) = s ^ 4 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using t9
  have tp10 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_1 * x.ofLp x_4 * (y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4 * y.ofLp x_1) = s ^ 4 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using t10
  have tp11 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_1 * x.ofLp x_4 * (y.ofLp x_1 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4) = s ^ 4 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using t11
  have tp12 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_1 * x.ofLp x_4 * (y.ofLp x_2 * y.ofLp x_1 * y.ofLp x_3 * y.ofLp x_4) = s ^ 4 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using t12
  have tp13 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_1 * (y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4 * y.ofLp x_1) = s ^ 4 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using t13
  have tp14 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_1 * (y.ofLp x_1 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4) = s ^ 4 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using t14
  have tp15 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_1 * (y.ofLp x_2 * y.ofLp x_1 * y.ofLp x_3 * y.ofLp x_4) = s ^ 4 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using t15
  have tp16 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_1 * (y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_1 * y.ofLp x_4) = s ^ 4 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using t16
  simp_rw [tp0, tp1, tp2, tp3, tp4, tp5, tp6, tp7, tp8, tp9, tp10, tp11, tp12, tp13, tp14, tp15, tp16]
  ring

set_option maxHeartbeats 2000000000 in
lemma sum_B6a_B6b (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, B6a x p * B6b y p = 20 * (@inner ℝ _ _ x y) ^ 4 + 30 * (@inner ℝ _ _ x y) ^ 2 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [B6a, B6b]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 800000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 800000000 }) only [mul_ite, mul_zero, ite_mul, zero_mul, one_mul]
  simp (config := { maxSteps := 800000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 800000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 800000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 800000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 800000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp_rw (config := { maxSteps := 800000000 }) [sum_ite_prop_zero]
  try simp (config := { maxSteps := 800000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp_rw (config := { maxSteps := 800000000 }) [sum_ite_prop_zero]
  try simp (config := { maxSteps := 800000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp only [sq]
  try ring_nf
  have a1 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * y.ofLp x_1 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4 = s ^ 4 := by
    have rr : ∀ a b c d : Fin 8,
        x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) := by
      intros; ring
    simp_rw [rr, factor4, ← hs]
    ring
  have a2 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 ^ 2 * x.ofLp x_3 * x.ofLp x_4 * y.ofLp x_1 ^ 2 * y.ofLp x_3 * y.ofLp x_4 = s ^ 2 := by
    have rr : ∀ a b c d : Fin 8,
        x.ofLp b ^ 2 * x.ofLp c * x.ofLp d * y.ofLp a ^ 2 * y.ofLp c * y.ofLp d =
        (y.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) := by
      intros; ring
    simp_rw [rr, factor4, hyn, hxn, ← hs]
    ring
  have a3 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_4 * y.ofLp x_1 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4 = s ^ 4 := by
    have rr : ∀ a b c d : Fin 8,
        x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp d * y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) := by
      intros; ring
    simp_rw [rr, factor4, ← hs]
    ring
  have a4 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_1 * x.ofLp x_4 * y.ofLp x_1 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4 = s ^ 4 := by
    have rr : ∀ a b c d : Fin 8,
        x.ofLp b * x.ofLp c * x.ofLp a * x.ofLp d * y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) := by
      intros; ring
    simp_rw [rr, factor4, ← hs]
    ring
  have a5 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_1 * y.ofLp x_1 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4 = s ^ 4 := by
    have rr : ∀ a b c d : Fin 8,
        x.ofLp b * x.ofLp c * x.ofLp d * x.ofLp a * y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) := by
      intros; ring
    simp_rw [rr, factor4, ← hs]
    ring
  have a6 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_3 ^ 2 * x.ofLp x_4 * y.ofLp x_1 ^ 2 * y.ofLp x_2 * y.ofLp x_4 = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c; arg 2; ext d
      rw [show x.ofLp b * x.ofLp c ^ 2 * x.ofLp d * y.ofLp a ^ 2 * y.ofLp b * y.ofLp d =
          (y.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) * (x.ofLp d * y.ofLp d) from by
        ring]
    simp_rw [factor4, hyn, hxn, ← hs]
    ring
  have a7 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 ^ 2 * y.ofLp x_1 ^ 2 * y.ofLp x_2 * y.ofLp x_3 = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c; arg 2; ext d
      rw [show x.ofLp b * x.ofLp c * x.ofLp d ^ 2 * y.ofLp a ^ 2 * y.ofLp b * y.ofLp c =
          (y.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * x.ofLp d) from by
        ring]
    simp_rw [factor4, hyn, hxn, ← hs]
    ring
  simp_rw [a1, a2, a3, a4, a5, a6, a7]
  ring

set_option maxHeartbeats 2000000000 in
lemma sum_B6b_B6b (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, B6b x p * B6b y p = 140 * (@inner ℝ _ _ x y) ^ 4 + 30 * (@inner ℝ _ _ x y) ^ 2 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [B6b]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 1000000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 1000000000 }) only [mul_ite, mul_zero, ite_mul, zero_mul, one_mul]
  simp (config := { maxSteps := 1000000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 1000000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 1000000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 1000000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 1000000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp_rw (config := { maxSteps := 1000000000 }) [sum_ite_prop_zero]
  try simp (config := { maxSteps := 1000000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp_rw (config := { maxSteps := 1000000000 }) [sum_ite_prop_zero]
  try simp (config := { maxSteps := 1000000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp only [sq]
  try ring_nf
  try simp_rw (config := { maxSteps := 1000000000 }) [sum_ite_prop_zero]
  try simp (config := { maxSteps := 1000000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp_rw (config := { maxSteps := 1000000000 }) [sum_ite_prop_zero]
  try simp (config := { maxSteps := 1000000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp_rw (config := { maxSteps := 1000000000 }) [sum_ite_prop_zero]
  try simp (config := { maxSteps := 1000000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have b1 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8, ∑ x_5 : Fin 8,
      x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_5 * y.ofLp x_1 * y.ofLp x_3 * y.ofLp x_4 * y.ofLp x_5 = 8 * s ^ 4 := by
    conv_lhs =>
      arg 2; ext a
      arg 2; ext b
      arg 2; ext c
      arg 2; ext d
      arg 2; ext e
      rw [show x.ofLp a * x.ofLp c * x.ofLp d * x.ofLp e * y.ofLp a * y.ofLp c * y.ofLp d * y.ofLp e =
          (x.ofLp a * y.ofLp a) * (1 : ℝ) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) from by
        ring]
    try simp_rw [mul_assoc, mul_left_comm, mul_comm]
    have hfac :
        ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, ∑ d : Fin 8, ∑ e : Fin 8,
          (x.ofLp a * y.ofLp a) * (1 : ℝ) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) =
        (∑ a : Fin 8, x.ofLp a * y.ofLp a) * (∑ b : Fin 8, (1 : ℝ)) *
          (∑ c : Fin 8, x.ofLp c * y.ofLp c) * (∑ d : Fin 8, x.ofLp d * y.ofLp d) *
          (∑ e : Fin 8, x.ofLp e * y.ofLp e) := by
      simpa using
        (factor5 (fun a : Fin 8 => x.ofLp a * y.ofLp a)
          (fun _ : Fin 8 => (1 : ℝ))
          (fun c : Fin 8 => x.ofLp c * y.ofLp c)
          (fun d : Fin 8 => x.ofLp d * y.ofLp d)
          (fun e : Fin 8 => x.ofLp e * y.ofLp e))
    simp_rw [hfac, ← hs]
    simp [Finset.sum_const, Fintype.card_fin]
    ring

  have b2 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * y.ofLp x_1 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4 = s ^ 4 := by
    conv_lhs =>
      arg 2; ext a
      arg 2; ext b
      arg 2; ext c
      arg 2; ext d
      rw [show x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) from by
        ring]
    try simp_rw [mul_assoc, mul_left_comm, mul_comm]
    simp_rw [factor4, ← hs]
    ring

  have b3 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * y.ofLp x_1 * y.ofLp x_3 * y.ofLp x_2 * y.ofLp x_4 = s ^ 4 := by
    conv_lhs =>
      arg 2; ext a
      arg 2; ext b
      arg 2; ext c
      arg 2; ext d
      rw [show x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * y.ofLp a * y.ofLp c * y.ofLp b * y.ofLp d =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) from by
        ring]
    try simp_rw [mul_assoc, mul_left_comm, mul_comm]
    simp_rw [factor4, ← hs]
    ring

  have b4 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * y.ofLp x_1 * y.ofLp x_3 * y.ofLp x_4 * y.ofLp x_2 = s ^ 4 := by
    conv_lhs =>
      arg 2; ext a
      arg 2; ext b
      arg 2; ext c
      arg 2; ext d
      rw [show x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * y.ofLp a * y.ofLp c * y.ofLp d * y.ofLp b =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) from by
        ring]
    try simp_rw [mul_assoc, mul_left_comm, mul_comm]
    simp_rw [factor4, ← hs]
    ring

  have b5 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 ^ 2 * x.ofLp x_4 * y.ofLp x_1 * y.ofLp x_3 ^ 2 * y.ofLp x_4 = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a
      arg 2; ext b
      arg 2; ext c
      arg 2; ext d
      rw [show x.ofLp a * x.ofLp b ^ 2 * x.ofLp d * y.ofLp a * y.ofLp c ^ 2 * y.ofLp d =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (y.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) from by
        ring]
    try simp_rw [mul_assoc, mul_left_comm, mul_comm]
    simp_rw [factor4, hxn, hyn, ← hs]
    ring

  have b6 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 ^ 2 * x.ofLp x_3 * y.ofLp x_1 * y.ofLp x_3 * y.ofLp x_4 ^ 2 = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a
      arg 2; ext b
      arg 2; ext c
      arg 2; ext d
      rw [show x.ofLp a * x.ofLp b ^ 2 * x.ofLp c * y.ofLp a * y.ofLp c * y.ofLp d ^ 2 =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) * (y.ofLp d * y.ofLp d) from by
        ring]
    try simp_rw [mul_assoc, mul_left_comm, mul_comm]
    simp_rw [factor4, hxn, hyn, ← hs]
    ring

  have b7 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_2 * x.ofLp x_4 * y.ofLp x_1 * y.ofLp x_3 * y.ofLp x_2 * y.ofLp x_4 = s ^ 4 := by
    conv_lhs =>
      arg 2; ext a
      arg 2; ext b
      arg 2; ext c
      arg 2; ext d
      rw [show x.ofLp a * x.ofLp c * x.ofLp b * x.ofLp d * y.ofLp a * y.ofLp c * y.ofLp b * y.ofLp d =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) from by
        ring]
    try simp_rw [mul_assoc, mul_left_comm, mul_comm]
    simp_rw [factor4, ← hs]
    ring

  have b8 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_2 * x.ofLp x_4 * y.ofLp x_1 * y.ofLp x_3 * y.ofLp x_4 * y.ofLp x_2 = s ^ 4 := by
    conv_lhs =>
      arg 2; ext a
      arg 2; ext b
      arg 2; ext c
      arg 2; ext d
      rw [show x.ofLp a * x.ofLp c * x.ofLp b * x.ofLp d * y.ofLp a * y.ofLp c * y.ofLp d * y.ofLp b =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) from by
        ring]
    try simp_rw [mul_assoc, mul_left_comm, mul_comm]
    simp_rw [factor4, ← hs]
    ring

  have b9 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_2 * x.ofLp x_4 * y.ofLp x_1 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4 = s ^ 4 := by
    conv_lhs =>
      arg 2; ext a
      arg 2; ext b
      arg 2; ext c
      arg 2; ext d
      rw [show x.ofLp a * x.ofLp c * x.ofLp b * x.ofLp d * y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) from by
        ring]
    try simp_rw [mul_assoc, mul_left_comm, mul_comm]
    simp_rw [factor4, ← hs]
    ring

  have b10 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_2 * y.ofLp x_1 * y.ofLp x_3 * y.ofLp x_4 * y.ofLp x_2 = s ^ 4 := by
    conv_lhs =>
      arg 2; ext a
      arg 2; ext b
      arg 2; ext c
      arg 2; ext d
      rw [show x.ofLp a * x.ofLp c * x.ofLp d * x.ofLp b * y.ofLp a * y.ofLp c * y.ofLp d * y.ofLp b =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) from by
        ring]
    try simp_rw [mul_assoc, mul_left_comm, mul_comm]
    simp_rw [factor4, ← hs]
    ring

  have b11 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_2 * y.ofLp x_1 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4 = s ^ 4 := by
    conv_lhs =>
      arg 2; ext a
      arg 2; ext b
      arg 2; ext c
      arg 2; ext d
      rw [show x.ofLp a * x.ofLp c * x.ofLp d * x.ofLp b * y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) from by
        ring]
    try simp_rw [mul_assoc, mul_left_comm, mul_comm]
    simp_rw [factor4, ← hs]
    ring

  have b12 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_4 * x.ofLp x_2 * y.ofLp x_1 * y.ofLp x_3 * y.ofLp x_2 * y.ofLp x_4 = s ^ 4 := by
    conv_lhs =>
      arg 2; ext a
      arg 2; ext b
      arg 2; ext c
      arg 2; ext d
      rw [show x.ofLp a * x.ofLp c * x.ofLp d * x.ofLp b * y.ofLp a * y.ofLp c * y.ofLp b * y.ofLp d =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) from by
        ring]
    try simp_rw [mul_assoc, mul_left_comm, mul_comm]
    simp_rw [factor4, ← hs]
    ring

  have b13 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_3 ^ 2 * x.ofLp x_4 * y.ofLp x_1 * y.ofLp x_2 ^ 2 * y.ofLp x_4 = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a
      arg 2; ext b
      arg 2; ext c
      arg 2; ext d
      rw [show x.ofLp a * x.ofLp c ^ 2 * x.ofLp d * y.ofLp a * y.ofLp b ^ 2 * y.ofLp d =
          (x.ofLp a * y.ofLp a) * (y.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) * (x.ofLp d * y.ofLp d) from by
        ring]
    try simp_rw [mul_assoc, mul_left_comm, mul_comm]
    simp_rw [factor4, hxn, hyn, ← hs]
    ring

  have b14 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8, ∑ x_5 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_4 * x.ofLp x_5 * y.ofLp x_1 * y.ofLp x_2 * y.ofLp x_4 * y.ofLp x_5 = 8 * s ^ 4 := by
    conv_lhs =>
      arg 2; ext a
      arg 2; ext b
      arg 2; ext c
      arg 2; ext d
      arg 2; ext e
      rw [show x.ofLp a * x.ofLp b * x.ofLp d * x.ofLp e * y.ofLp a * y.ofLp b * y.ofLp d * y.ofLp e =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (1 : ℝ) * (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) from by
        ring]
    try simp_rw [mul_assoc, mul_left_comm, mul_comm]
    have hfac :
        ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, ∑ d : Fin 8, ∑ e : Fin 8,
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (1 : ℝ) * (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) =
        (∑ a : Fin 8, x.ofLp a * y.ofLp a) * (∑ b : Fin 8, x.ofLp b * y.ofLp b) *
          (∑ c : Fin 8, (1 : ℝ)) * (∑ d : Fin 8, x.ofLp d * y.ofLp d) *
          (∑ e : Fin 8, x.ofLp e * y.ofLp e) := by
      simpa using
        (factor5 (fun a : Fin 8 => x.ofLp a * y.ofLp a)
          (fun b : Fin 8 => x.ofLp b * y.ofLp b)
          (fun _ : Fin 8 => (1 : ℝ))
          (fun d : Fin 8 => x.ofLp d * y.ofLp d)
          (fun e : Fin 8 => x.ofLp e * y.ofLp e))
    simp_rw [hfac, ← hs]
    simp [Finset.sum_const, Fintype.card_fin]
    ring

  have b15 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * y.ofLp x_1 * y.ofLp x_2 * y.ofLp x_4 * y.ofLp x_3 = s ^ 4 := by
    conv_lhs =>
      arg 2; ext a
      arg 2; ext b
      arg 2; ext c
      arg 2; ext d
      rw [show x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * y.ofLp a * y.ofLp b * y.ofLp d * y.ofLp c =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) from by
        ring]
    try simp_rw [mul_assoc, mul_left_comm, mul_comm]
    simp_rw [factor4, ← hs]
    ring

  have b16 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 ^ 2 * y.ofLp x_1 * y.ofLp x_2 * y.ofLp x_4 ^ 2 = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a
      arg 2; ext b
      arg 2; ext c
      arg 2; ext d
      rw [show x.ofLp a * x.ofLp b * x.ofLp c ^ 2 * y.ofLp a * y.ofLp b * y.ofLp d ^ 2 =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) * (y.ofLp d * y.ofLp d) from by
        ring]
    try simp_rw [mul_assoc, mul_left_comm, mul_comm]
    simp_rw [factor4, hxn, hyn, ← hs]
    ring

  have b17 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_4 * x.ofLp x_3 * y.ofLp x_1 * y.ofLp x_2 * y.ofLp x_4 * y.ofLp x_3 = s ^ 4 := by
    conv_lhs =>
      arg 2; ext a
      arg 2; ext b
      arg 2; ext c
      arg 2; ext d
      rw [show x.ofLp a * x.ofLp b * x.ofLp d * x.ofLp c * y.ofLp a * y.ofLp b * y.ofLp d * y.ofLp c =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) from by
        ring]
    try simp_rw [mul_assoc, mul_left_comm, mul_comm]
    simp_rw [factor4, ← hs]
    ring

  have b18 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_4 * x.ofLp x_3 * y.ofLp x_1 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4 = s ^ 4 := by
    conv_lhs =>
      arg 2; ext a
      arg 2; ext b
      arg 2; ext c
      arg 2; ext d
      rw [show x.ofLp a * x.ofLp b * x.ofLp d * x.ofLp c * y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) from by
        ring]
    try simp_rw [mul_assoc, mul_left_comm, mul_comm]
    simp_rw [factor4, ← hs]
    ring

  have b19 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_4 ^ 2 * y.ofLp x_1 * y.ofLp x_2 ^ 2 * y.ofLp x_3 = s ^ 2 := by
    have rr : ∀ a b c d : Fin 8,
        x.ofLp a * x.ofLp c * x.ofLp d ^ 2 * y.ofLp a * y.ofLp b ^ 2 * y.ofLp c =
        (x.ofLp a * y.ofLp a) * (y.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * x.ofLp d) := by
      intros; ring
    simp_rw [rr, factor4, hxn, hyn, ← hs]
    ring

  have b20 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_4 ^ 2 * y.ofLp x_1 * y.ofLp x_2 * y.ofLp x_3 ^ 2 = s ^ 2 := by
    have rr : ∀ a b c d : Fin 8,
        x.ofLp a * x.ofLp b * x.ofLp d ^ 2 * y.ofLp a * y.ofLp b * y.ofLp c ^ 2 =
        (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (y.ofLp c * y.ofLp c) * (x.ofLp d * x.ofLp d) := by
      intros; ring
    simp_rw [rr, factor4, hxn, hyn, ← hs]
    ring

  have b21 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8, ∑ x_5 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_5 * y.ofLp x_1 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_5 = 8 * s ^ 4 := by
    conv_lhs =>
      arg 2; ext a
      arg 2; ext b
      arg 2; ext c
      arg 2; ext d
      arg 2; ext e
      rw [show x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp e * y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp e =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (1 : ℝ) * (x.ofLp e * y.ofLp e) from by
        ring]
    try simp_rw [mul_assoc, mul_left_comm, mul_comm]
    have hfac :
        ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, ∑ d : Fin 8, ∑ e : Fin 8,
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (1 : ℝ) * (x.ofLp e * y.ofLp e) =
        (∑ a : Fin 8, x.ofLp a * y.ofLp a) * (∑ b : Fin 8, x.ofLp b * y.ofLp b) *
          (∑ c : Fin 8, x.ofLp c * y.ofLp c) * (∑ d : Fin 8, (1 : ℝ)) *
          (∑ e : Fin 8, x.ofLp e * y.ofLp e) := by
      simpa using
        (factor5 (fun a : Fin 8 => x.ofLp a * y.ofLp a)
          (fun b : Fin 8 => x.ofLp b * y.ofLp b)
          (fun c : Fin 8 => x.ofLp c * y.ofLp c)
          (fun _ : Fin 8 => (1 : ℝ))
          (fun e : Fin 8 => x.ofLp e * y.ofLp e))
    simp_rw [hfac, ← hs]
    simp [Finset.sum_const, Fintype.card_fin]
    ring

  have b22 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8, ∑ x_5 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 * y.ofLp x_1 * y.ofLp x_2 * y.ofLp x_3 * y.ofLp x_4 = 8 * s ^ 4 := by
    have h5 : ∀ a b c d : Fin 8,
        (∑ e : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d) =
          8 * (x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d) := by
      intro a b c d
      simp [Finset.sum_const, Fintype.card_fin]
    conv_lhs =>
      arg 2; ext a
      arg 2; ext b
      arg 2; ext c
      arg 2; ext d
      rw [h5 a b c d]
      rw [show 8 * (x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d) =
          (x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp d * y.ofLp a * y.ofLp b * y.ofLp c * y.ofLp d) * 8 from by
        ring]
    simp_rw [← Finset.sum_mul]
    rw [b2]
    ring
  simp_rw [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22]
  ring

end TestBBSplit
