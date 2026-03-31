import KissingNumber.PSD6Defs
import KissingNumber.TestBBSplit
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators RealInnerProductSpace
open Real Finset
open PSD6Defs

noncomputable section

namespace TestBCSplit

private abbrev T6k := PSD6Defs.T6

/-! ## C6 decomposition: C6 = C6a + C6b

C6a: terms where position 'a' (p.1) is one of the two "free" indices.
C6b: terms where position 'a' is NOT a free index.
-/

def C6a (x : EuclideanSpace ℝ (Fin 8)) (p : T6k) : ℝ :=
  let a := p.1; let b := p.2.1; let c := p.2.2.1
  let d := p.2.2.2.1; let e := p.2.2.2.2.1; let f := p.2.2.2.2.2
  x a * x b * ((if c=d then 1 else 0)*(if e=f then 1 else 0) + (if c=e then 1 else 0)*(if d=f then 1 else 0) + (if c=f then 1 else 0)*(if d=e then 1 else 0))
  + x a * x c * ((if b=d then 1 else 0)*(if e=f then 1 else 0) + (if b=e then 1 else 0)*(if d=f then 1 else 0) + (if b=f then 1 else 0)*(if d=e then 1 else 0))
  + x a * x d * ((if b=c then 1 else 0)*(if e=f then 1 else 0) + (if b=e then 1 else 0)*(if c=f then 1 else 0) + (if b=f then 1 else 0)*(if c=e then 1 else 0))
  + x a * x e * ((if b=c then 1 else 0)*(if d=f then 1 else 0) + (if b=d then 1 else 0)*(if c=f then 1 else 0) + (if b=f then 1 else 0)*(if c=d then 1 else 0))
  + x a * x f * ((if b=c then 1 else 0)*(if d=e then 1 else 0) + (if b=d then 1 else 0)*(if c=e then 1 else 0) + (if b=e then 1 else 0)*(if c=d then 1 else 0))

def C6b (x : EuclideanSpace ℝ (Fin 8)) (p : T6k) : ℝ :=
  let a := p.1; let b := p.2.1; let c := p.2.2.1
  let d := p.2.2.2.1; let e := p.2.2.2.2.1; let f := p.2.2.2.2.2
  x b * x c * ((if a=d then 1 else 0)*(if e=f then 1 else 0) + (if a=e then 1 else 0)*(if d=f then 1 else 0) + (if a=f then 1 else 0)*(if d=e then 1 else 0))
  + x b * x d * ((if a=c then 1 else 0)*(if e=f then 1 else 0) + (if a=e then 1 else 0)*(if c=f then 1 else 0) + (if a=f then 1 else 0)*(if c=e then 1 else 0))
  + x b * x e * ((if a=c then 1 else 0)*(if d=f then 1 else 0) + (if a=d then 1 else 0)*(if c=f then 1 else 0) + (if a=f then 1 else 0)*(if c=d then 1 else 0))
  + x b * x f * ((if a=c then 1 else 0)*(if d=e then 1 else 0) + (if a=d then 1 else 0)*(if c=e then 1 else 0) + (if a=e then 1 else 0)*(if c=d then 1 else 0))
  + x c * x d * ((if a=b then 1 else 0)*(if e=f then 1 else 0) + (if a=e then 1 else 0)*(if b=f then 1 else 0) + (if a=f then 1 else 0)*(if b=e then 1 else 0))
  + x c * x e * ((if a=b then 1 else 0)*(if d=f then 1 else 0) + (if a=d then 1 else 0)*(if b=f then 1 else 0) + (if a=f then 1 else 0)*(if b=d then 1 else 0))
  + x c * x f * ((if a=b then 1 else 0)*(if d=e then 1 else 0) + (if a=d then 1 else 0)*(if b=e then 1 else 0) + (if a=e then 1 else 0)*(if b=d then 1 else 0))
  + x d * x e * ((if a=b then 1 else 0)*(if c=f then 1 else 0) + (if a=c then 1 else 0)*(if b=f then 1 else 0) + (if a=f then 1 else 0)*(if b=c then 1 else 0))
  + x d * x f * ((if a=b then 1 else 0)*(if c=e then 1 else 0) + (if a=c then 1 else 0)*(if b=e then 1 else 0) + (if a=e then 1 else 0)*(if b=c then 1 else 0))
  + x e * x f * ((if a=b then 1 else 0)*(if c=d then 1 else 0) + (if a=c then 1 else 0)*(if b=d then 1 else 0) + (if a=d then 1 else 0)*(if b=c then 1 else 0))

lemma C6_split (x : EuclideanSpace ℝ (Fin 8)) (p : T6k) :
    C6 x p = C6a x p + C6b x p := by
  simp only [C6, C6a, C6b]
  ring

/-! ## Direct proof of sum_BC via simp chain + rearrangement -/

set_option maxHeartbeats 4000000000 in
lemma sum_B6a_C6a (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, TestBBSplit.B6a x p * C6a y p =
    60 * (@inner ℝ _ _ x y) ^ 2 + 15 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [TestBBSplit.B6a, C6a]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 400000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 400000000 }) only [mul_ite, mul_zero, ite_mul, zero_mul, one_mul]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [mul_one]
  have rA1 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp b * (y.ofLp c * y.ofLp c) =
      (y.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have rA2 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp a * x.ofLp b * (y.ofLp c * y.ofLp c) =
      (y.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have rA3 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp a * (y.ofLp c * y.ofLp c) =
      (y.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) := by intros; ring
  have rB1 : ∀ a b c : Fin 8, x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp c * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have rB5 : ∀ a b c : Fin 8, x.ofLp b * x.ofLp c * x.ofLp c * x.ofLp a * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have rB11 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp c * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) := by intros; ring
  have rB4 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp c * x.ofLp b * x.ofLp c * (y.ofLp b * y.ofLp a) =
      (x.ofLp b * y.ofLp b) * (x.ofLp a * y.ofLp a) * (x.ofLp c * x.ofLp c) := by intros; ring
  have rB6 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp c * x.ofLp a * x.ofLp b * (y.ofLp b * y.ofLp c) =
      (x.ofLp b * y.ofLp b) * (x.ofLp a * x.ofLp a) * (x.ofLp c * y.ofLp c) := by intros; ring
  have rB8 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp a * x.ofLp b * x.ofLp c * (y.ofLp c * y.ofLp b) =
      (x.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  have rB9 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp a * (y.ofLp c * y.ofLp b) =
      (x.ofLp c * y.ofLp c) * (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  have rC1 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp c * x.ofLp b * (y.ofLp a * y.ofLp c) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) := by intros; ring
  have rC2 : ∀ a b c : Fin 8, x.ofLp b * x.ofLp a * x.ofLp c * x.ofLp b * (y.ofLp a * y.ofLp c) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) := by intros; ring
  have rC3 : ∀ a b c : Fin 8, x.ofLp b * x.ofLp b * x.ofLp a * x.ofLp c * (y.ofLp a * y.ofLp c) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) := by intros; ring
  have rC4 : ∀ a b c : Fin 8, x.ofLp b * x.ofLp a * x.ofLp b * x.ofLp c * (y.ofLp a * y.ofLp c) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) := by intros; ring
  have rC5 : ∀ a b c : Fin 8, x.ofLp a * x.ofLp b * x.ofLp b * x.ofLp c * (y.ofLp a * y.ofLp c) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) := by intros; ring
  simp_rw [rA1, rA2, rA3, rB1, rB4, rB5, rB6, rB8, rB9, rB11, rC1, rC2, rC3, rC4, rC5]
  simp_rw [factor3, hxn, hyn, ← hs]
  ring

set_option maxHeartbeats 4000000000 in
lemma sum_B6a_C6b (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, TestBBSplit.B6a x p * C6b y p =
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
  -- rr lemmas for parenthesized y-factor bodies: x*x*x*x*(y*y)
  have rr1 : ∀ a b d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp d * x.ofLp d * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have rr2 : ∀ a b d : Fin 8, x.ofLp a * x.ofLp b * x.ofLp d * x.ofLp d * (y.ofLp b * y.ofLp a) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have rr3 : ∀ a b d : Fin 8, x.ofLp a * x.ofLp d * x.ofLp b * x.ofLp d * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have rr4 : ∀ a b d : Fin 8, x.ofLp a * x.ofLp d * x.ofLp b * x.ofLp d * (y.ofLp b * y.ofLp a) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have rr5 : ∀ a b d : Fin 8, x.ofLp a * x.ofLp d * x.ofLp d * x.ofLp b * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have rr6 : ∀ a b d : Fin 8, x.ofLp a * x.ofLp d * x.ofLp d * x.ofLp b * (y.ofLp b * y.ofLp a) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have rr7 : ∀ a b d : Fin 8, x.ofLp d * x.ofLp a * x.ofLp b * x.ofLp d * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have rr8 : ∀ a b d : Fin 8, x.ofLp d * x.ofLp a * x.ofLp b * x.ofLp d * (y.ofLp b * y.ofLp a) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have rr9 : ∀ a b d : Fin 8, x.ofLp d * x.ofLp a * x.ofLp d * x.ofLp b * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have rr10 : ∀ a b d : Fin 8, x.ofLp d * x.ofLp a * x.ofLp d * x.ofLp b * (y.ofLp b * y.ofLp a) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have rr11 : ∀ a b d : Fin 8, x.ofLp d * x.ofLp d * x.ofLp a * x.ofLp b * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  have rr12 : ∀ a b d : Fin 8, x.ofLp d * x.ofLp d * x.ofLp a * x.ofLp b * (y.ofLp b * y.ofLp a) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp d * x.ofLp d) := by intros; ring
  simp_rw [rr1, rr2, rr3, rr4, rr5, rr6, rr7, rr8, rr9, rr10, rr11, rr12]
  -- factor3 handles sums matching f(a)*g(b)*h(c)
  simp_rw [factor3, hxn, ← hs]
  -- ring_nf normalizes remaining sums (x*x → x^2, etc.)
  ring_nf
  -- Handle remaining interleaved sums via conv+have
  have h_s1 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8,
      x.ofLp x_2 * y.ofLp x_2 * x.ofLp x_1 * y.ofLp x_1 * x.ofLp x_3 ^ 2 = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c
      rw [show x.ofLp b * y.ofLp b * x.ofLp a * y.ofLp a * x.ofLp c ^ 2 =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) from by ring]
    simp_rw [factor3, hxn, ← hs]; ring
  have h_s2 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8,
      x.ofLp x_2 * y.ofLp x_2 * x.ofLp x_3 * y.ofLp x_3 * x.ofLp x_1 ^ 2 = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c
      rw [show x.ofLp b * y.ofLp b * x.ofLp c * y.ofLp c * x.ofLp a ^ 2 =
          (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) from by ring]
    simp_rw [factor3, hxn, ← hs]; ring
  have h_s3 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8,
      x.ofLp x_3 * y.ofLp x_3 * x.ofLp x_1 * y.ofLp x_1 * x.ofLp x_2 ^ 2 = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c
      rw [show x.ofLp c * y.ofLp c * x.ofLp a * y.ofLp a * x.ofLp b ^ 2 =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) from by ring]
    simp_rw [factor3, hxn, ← hs]; ring
  have h_s4 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8,
      x.ofLp x_1 * y.ofLp x_1 * x.ofLp x_3 * y.ofLp x_3 * x.ofLp x_2 ^ 2 = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c
      rw [show x.ofLp a * y.ofLp a * x.ofLp c * y.ofLp c * x.ofLp b ^ 2 =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) from by ring]
    simp_rw [factor3, hxn, ← hs]; ring
  have h_s5 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_2 * y.ofLp x_2 * x.ofLp x_4 * y.ofLp x_4 * x.ofLp x_3 ^ 2 = 8 * s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c; arg 2; ext d
      rw [show x.ofLp b * y.ofLp b * x.ofLp d * y.ofLp d * x.ofLp c ^ 2 =
          (1 : ℝ) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) * (x.ofLp d * y.ofLp d) from by ring]
    simp_rw [factor4, hxn, ← hs]
    simp [Finset.sum_const, Fintype.card_fin]; ring
  have h_s6 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_3 * y.ofLp x_3 * x.ofLp x_4 * y.ofLp x_4 * x.ofLp x_2 ^ 2 = 8 * s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c; arg 2; ext d
      rw [show x.ofLp c * y.ofLp c * x.ofLp d * y.ofLp d * x.ofLp b ^ 2 =
          (1 : ℝ) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) from by ring]
    simp_rw [factor4, hxn, ← hs]
    simp [Finset.sum_const, Fintype.card_fin]; ring
  simp only [h_s1, h_s2, h_s3, h_s4]
  simp [Finset.sum_const, Fintype.card_fin]
  ring

set_option maxHeartbeats 4000000000 in
lemma sum_B6b_C6a (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, TestBBSplit.B6b x p * C6a y p =
    360 * (@inner ℝ _ _ x y) ^ 2 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [TestBBSplit.B6b, C6a]
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
  simp only [mul_one]
  ring_nf
  -- Triple sum lemmas: each body rewrites to factor3-compatible form
  have h_t1 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 ^ 2 * y.ofLp x_1 * y.ofLp x_2 = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c
      rw [show x.ofLp a * x.ofLp b * x.ofLp c ^ 2 * y.ofLp a * y.ofLp b =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) from by ring]
    simp_rw [factor3, hxn, ← hs]; ring
  have h_t2 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8,
      x.ofLp x_1 * x.ofLp x_3 ^ 2 * x.ofLp x_2 * y.ofLp x_1 * y.ofLp x_2 = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c
      rw [show x.ofLp a * x.ofLp c ^ 2 * x.ofLp b * y.ofLp a * y.ofLp b =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) from by ring]
    simp_rw [factor3, hxn, ← hs]; ring
  have h_t3 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8,
      x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_2 ^ 2 * y.ofLp x_1 * y.ofLp x_3 = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c
      rw [show x.ofLp a * x.ofLp c * x.ofLp b ^ 2 * y.ofLp a * y.ofLp c =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) from by ring]
    simp_rw [factor3, hxn, ← hs]; ring
  have h_t4 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 ^ 2 * x.ofLp x_3 * y.ofLp x_1 * y.ofLp x_3 = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c
      rw [show x.ofLp a * x.ofLp b ^ 2 * x.ofLp c * y.ofLp a * y.ofLp c =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) from by ring]
    simp_rw [factor3, hxn, ← hs]; ring
  -- Quad sum lemmas: unused variable gets (1 : ℝ) factor, use factor4
  have h_q1 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_4 ^ 2 * y.ofLp x_1 * y.ofLp x_2 = 8 * s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c; arg 2; ext d
      rw [show x.ofLp a * x.ofLp b * x.ofLp d ^ 2 * y.ofLp a * y.ofLp b =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (1 : ℝ) * (x.ofLp d * x.ofLp d) from by ring]
    simp_rw [factor4, hxn, ← hs]
    simp [Finset.sum_const, Fintype.card_fin]; ring
  have h_q2 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 ^ 2 * y.ofLp x_1 * y.ofLp x_2 = 8 * s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c; arg 2; ext d
      rw [show x.ofLp a * x.ofLp b * x.ofLp c ^ 2 * y.ofLp a * y.ofLp b =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) * (1 : ℝ) from by ring]
    simp_rw [factor4, hxn, ← hs]
    simp [Finset.sum_const, Fintype.card_fin]; ring
  have h_q3 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_3 * x.ofLp x_4 ^ 2 * y.ofLp x_1 * y.ofLp x_3 = 8 * s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c; arg 2; ext d
      rw [show x.ofLp a * x.ofLp c * x.ofLp d ^ 2 * y.ofLp a * y.ofLp c =
          (x.ofLp a * y.ofLp a) * (1 : ℝ) * (x.ofLp c * y.ofLp c) * (x.ofLp d * x.ofLp d) from by ring]
    simp_rw [factor4, hxn, ← hs]
    simp [Finset.sum_const, Fintype.card_fin]; ring
  have h_q4 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 ^ 2 * x.ofLp x_3 * y.ofLp x_1 * y.ofLp x_3 = 8 * s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c; arg 2; ext d
      rw [show x.ofLp a * x.ofLp b ^ 2 * x.ofLp c * y.ofLp a * y.ofLp c =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) * (1 : ℝ) from by ring]
    simp_rw [factor4, hxn, ← hs]
    simp [Finset.sum_const, Fintype.card_fin]; ring
  have h_q5 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_3 ^ 2 * x.ofLp x_4 * y.ofLp x_1 * y.ofLp x_4 = 8 * s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c; arg 2; ext d
      rw [show x.ofLp a * x.ofLp c ^ 2 * x.ofLp d * y.ofLp a * y.ofLp d =
          (x.ofLp a * y.ofLp a) * (1 : ℝ) * (x.ofLp c * x.ofLp c) * (x.ofLp d * y.ofLp d) from by ring]
    simp_rw [factor4, hxn, ← hs]
    simp [Finset.sum_const, Fintype.card_fin]; ring
  have h_q6 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 ^ 2 * x.ofLp x_4 * y.ofLp x_1 * y.ofLp x_4 = 8 * s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c; arg 2; ext d
      rw [show x.ofLp a * x.ofLp b ^ 2 * x.ofLp d * y.ofLp a * y.ofLp d =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (1 : ℝ) * (x.ofLp d * y.ofLp d) from by ring]
    simp_rw [factor4, hxn, ← hs]
    simp [Finset.sum_const, Fintype.card_fin]; ring
  simp only [h_t1, h_t2, h_t3, h_t4, h_q1, h_q2, h_q3, h_q4, h_q5, h_q6]
  ring

set_option maxHeartbeats 4000000000 in
lemma sum_B6b_C6b (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, TestBBSplit.B6b x p * C6b y p =
    480 * (@inner ℝ _ _ x y) ^ 2 + 30 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [TestBBSplit.B6b, C6b]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 2000000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 2000000000 }) only [mul_ite, mul_zero, ite_mul, zero_mul, one_mul]
  simp (config := { maxSteps := 2000000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 2000000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 2000000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 2000000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 2000000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  try simp_rw (config := { maxSteps := 2000000000 }) [sum_ite_prop_zero]
  try simp (config := { maxSteps := 2000000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [mul_one]
  ring_nf
  -- Constant sums (all squared factors, = 1)
  have h_c1 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8,
      x.ofLp x_1 ^ 2 * x.ofLp x_3 ^ 2 * y.ofLp x_2 ^ 2 = 1 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c
      rw [show x.ofLp a ^ 2 * x.ofLp c ^ 2 * y.ofLp b ^ 2 =
          (x.ofLp a * x.ofLp a) * (y.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) from by ring]
    simp_rw [factor3, hxn, hyn]; norm_num
  have h_c2 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8,
      x.ofLp x_1 ^ 2 * x.ofLp x_2 ^ 2 * y.ofLp x_3 ^ 2 = 1 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c
      rw [show x.ofLp a ^ 2 * x.ofLp b ^ 2 * y.ofLp c ^ 2 =
          (x.ofLp a * x.ofLp a) * (x.ofLp b * x.ofLp b) * (y.ofLp c * y.ofLp c) from by ring]
    simp_rw [factor3, hxn, hyn]; norm_num
  -- Triple sums (= s²)
  have h_t1 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 ^ 2 * y.ofLp x_1 * y.ofLp x_2 = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c
      rw [show x.ofLp a * x.ofLp b * x.ofLp c ^ 2 * y.ofLp a * y.ofLp b =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) from by ring]
    simp_rw [factor3, hxn, ← hs]; ring
  have h_t2 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8,
      x.ofLp x_1 ^ 2 * x.ofLp x_3 * x.ofLp x_2 * y.ofLp x_2 * y.ofLp x_3 = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c
      rw [show x.ofLp a ^ 2 * x.ofLp c * x.ofLp b * y.ofLp b * y.ofLp c =
          (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) from by ring]
    simp_rw [factor3, hxn, ← hs]; ring
  have h_t3 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 * x.ofLp x_3 ^ 2 * y.ofLp x_2 * y.ofLp x_1 = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c
      rw [show x.ofLp a * x.ofLp b * x.ofLp c ^ 2 * y.ofLp b * y.ofLp a =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * x.ofLp c) from by ring]
    simp_rw [factor3, hxn, ← hs]; ring
  have h_t4 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8,
      x.ofLp x_1 ^ 2 * x.ofLp x_2 * x.ofLp x_3 * y.ofLp x_2 * y.ofLp x_3 = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c
      rw [show x.ofLp a ^ 2 * x.ofLp b * x.ofLp c * y.ofLp b * y.ofLp c =
          (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) from by ring]
    simp_rw [factor3, hxn, ← hs]; ring
  have h_t5 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 ^ 2 * x.ofLp x_3 * y.ofLp x_1 * y.ofLp x_3 = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c
      rw [show x.ofLp a * x.ofLp b ^ 2 * x.ofLp c * y.ofLp a * y.ofLp c =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) from by ring]
    simp_rw [factor3, hxn, ← hs]; ring
  have h_t6 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8,
      x.ofLp x_1 ^ 2 * x.ofLp x_3 * x.ofLp x_2 * y.ofLp x_3 * y.ofLp x_2 = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c
      rw [show x.ofLp a ^ 2 * x.ofLp c * x.ofLp b * y.ofLp c * y.ofLp b =
          (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) from by ring]
    simp_rw [factor3, hxn, ← hs]; ring
  have h_t7 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8,
      x.ofLp x_1 * x.ofLp x_2 ^ 2 * x.ofLp x_3 * y.ofLp x_3 * y.ofLp x_1 = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c
      rw [show x.ofLp a * x.ofLp b ^ 2 * x.ofLp c * y.ofLp c * y.ofLp a =
          (x.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) from by ring]
    simp_rw [factor3, hxn, ← hs]; ring
  have h_t8 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8,
      x.ofLp x_1 ^ 2 * x.ofLp x_2 * x.ofLp x_3 * y.ofLp x_3 * y.ofLp x_2 = s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c
      rw [show x.ofLp a ^ 2 * x.ofLp b * x.ofLp c * y.ofLp c * y.ofLp b =
          (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) from by ring]
    simp_rw [factor3, hxn, ← hs]; ring
  -- Quad sums with phantom variable (= 8 * s²)
  have h_q1 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 ^ 2 * x.ofLp x_2 * x.ofLp x_3 * y.ofLp x_2 * y.ofLp x_3 = 8 * s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c; arg 2; ext d
      rw [show x.ofLp a ^ 2 * x.ofLp b * x.ofLp c * y.ofLp b * y.ofLp c =
          (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) * (x.ofLp c * y.ofLp c) * (1 : ℝ) from by ring]
    simp_rw [factor4, hxn, ← hs]
    simp [Finset.sum_const, Fintype.card_fin]; ring
  have h_q2 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 ^ 2 * x.ofLp x_2 * x.ofLp x_4 * y.ofLp x_2 * y.ofLp x_4 = 8 * s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c; arg 2; ext d
      rw [show x.ofLp a ^ 2 * x.ofLp b * x.ofLp d * y.ofLp b * y.ofLp d =
          (x.ofLp a * x.ofLp a) * (x.ofLp b * y.ofLp b) * (1 : ℝ) * (x.ofLp d * y.ofLp d) from by ring]
    simp_rw [factor4, hxn, ← hs]
    simp [Finset.sum_const, Fintype.card_fin]; ring
  have h_q3 : ∑ x_1 : Fin 8, ∑ x_2 : Fin 8, ∑ x_3 : Fin 8, ∑ x_4 : Fin 8,
      x.ofLp x_1 ^ 2 * x.ofLp x_3 * x.ofLp x_4 * y.ofLp x_3 * y.ofLp x_4 = 8 * s ^ 2 := by
    conv_lhs =>
      arg 2; ext a; arg 2; ext b; arg 2; ext c; arg 2; ext d
      rw [show x.ofLp a ^ 2 * x.ofLp c * x.ofLp d * y.ofLp c * y.ofLp d =
          (x.ofLp a * x.ofLp a) * (1 : ℝ) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) from by ring]
    simp_rw [factor4, hxn, ← hs]
    simp [Finset.sum_const, Fintype.card_fin]; ring
  simp only [h_c1, h_c2, h_t1, h_t2, h_t3, h_t4, h_t5, h_t6, h_t7, h_t8, h_q1, h_q2, h_q3]
  ring

end TestBCSplit
