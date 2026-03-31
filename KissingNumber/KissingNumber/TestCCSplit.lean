import KissingNumber.PSD6Defs
import KissingNumber.TestBCSplit
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators RealInnerProductSpace
open Real Finset
open PSD6Defs

noncomputable section

namespace TestCCSplit

private abbrev T6k := PSD6Defs.T6

/-! ## Fine-grained C6 decomposition for CC cross-terms

C6a = C6a1 + C6a2 (2 + 3 terms)
C6b = C6b1 + C6b2 + C6b3 (3 + 3 + 4 terms)
-/

def C6a1 (x : EuclideanSpace ℝ (Fin 8)) (p : T6k) : ℝ :=
  let a := p.1; let b := p.2.1; let c := p.2.2.1
  let d := p.2.2.2.1; let e := p.2.2.2.2.1; let f := p.2.2.2.2.2
  x a * x b * ((if c=d then 1 else 0)*(if e=f then 1 else 0) + (if c=e then 1 else 0)*(if d=f then 1 else 0) + (if c=f then 1 else 0)*(if d=e then 1 else 0))
  + x a * x c * ((if b=d then 1 else 0)*(if e=f then 1 else 0) + (if b=e then 1 else 0)*(if d=f then 1 else 0) + (if b=f then 1 else 0)*(if d=e then 1 else 0))

def C6a2 (x : EuclideanSpace ℝ (Fin 8)) (p : T6k) : ℝ :=
  let a := p.1; let b := p.2.1; let c := p.2.2.1
  let d := p.2.2.2.1; let e := p.2.2.2.2.1; let f := p.2.2.2.2.2
  x a * x d * ((if b=c then 1 else 0)*(if e=f then 1 else 0) + (if b=e then 1 else 0)*(if c=f then 1 else 0) + (if b=f then 1 else 0)*(if c=e then 1 else 0))
  + x a * x e * ((if b=c then 1 else 0)*(if d=f then 1 else 0) + (if b=d then 1 else 0)*(if c=f then 1 else 0) + (if b=f then 1 else 0)*(if c=d then 1 else 0))
  + x a * x f * ((if b=c then 1 else 0)*(if d=e then 1 else 0) + (if b=d then 1 else 0)*(if c=e then 1 else 0) + (if b=e then 1 else 0)*(if c=d then 1 else 0))

def C6b1 (x : EuclideanSpace ℝ (Fin 8)) (p : T6k) : ℝ :=
  let a := p.1; let b := p.2.1; let c := p.2.2.1
  let d := p.2.2.2.1; let e := p.2.2.2.2.1; let f := p.2.2.2.2.2
  x b * x c * ((if a=d then 1 else 0)*(if e=f then 1 else 0) + (if a=e then 1 else 0)*(if d=f then 1 else 0) + (if a=f then 1 else 0)*(if d=e then 1 else 0))
  + x b * x d * ((if a=c then 1 else 0)*(if e=f then 1 else 0) + (if a=e then 1 else 0)*(if c=f then 1 else 0) + (if a=f then 1 else 0)*(if c=e then 1 else 0))
  + x b * x e * ((if a=c then 1 else 0)*(if d=f then 1 else 0) + (if a=d then 1 else 0)*(if c=f then 1 else 0) + (if a=f then 1 else 0)*(if c=d then 1 else 0))

def C6b2 (x : EuclideanSpace ℝ (Fin 8)) (p : T6k) : ℝ :=
  let a := p.1; let b := p.2.1; let c := p.2.2.1
  let d := p.2.2.2.1; let e := p.2.2.2.2.1; let f := p.2.2.2.2.2
  x b * x f * ((if a=c then 1 else 0)*(if d=e then 1 else 0) + (if a=d then 1 else 0)*(if c=e then 1 else 0) + (if a=e then 1 else 0)*(if c=d then 1 else 0))
  + x c * x d * ((if a=b then 1 else 0)*(if e=f then 1 else 0) + (if a=e then 1 else 0)*(if b=f then 1 else 0) + (if a=f then 1 else 0)*(if b=e then 1 else 0))
  + x c * x e * ((if a=b then 1 else 0)*(if d=f then 1 else 0) + (if a=d then 1 else 0)*(if b=f then 1 else 0) + (if a=f then 1 else 0)*(if b=d then 1 else 0))

def C6b3 (x : EuclideanSpace ℝ (Fin 8)) (p : T6k) : ℝ :=
  let a := p.1; let b := p.2.1; let c := p.2.2.1
  let d := p.2.2.2.1; let e := p.2.2.2.2.1; let f := p.2.2.2.2.2
  x c * x f * ((if a=b then 1 else 0)*(if d=e then 1 else 0) + (if a=d then 1 else 0)*(if b=e then 1 else 0) + (if a=e then 1 else 0)*(if b=d then 1 else 0))
  + x d * x e * ((if a=b then 1 else 0)*(if c=f then 1 else 0) + (if a=c then 1 else 0)*(if b=f then 1 else 0) + (if a=f then 1 else 0)*(if b=c then 1 else 0))
  + x d * x f * ((if a=b then 1 else 0)*(if c=e then 1 else 0) + (if a=c then 1 else 0)*(if b=e then 1 else 0) + (if a=e then 1 else 0)*(if b=c then 1 else 0))
  + x e * x f * ((if a=b then 1 else 0)*(if c=d then 1 else 0) + (if a=c then 1 else 0)*(if b=d then 1 else 0) + (if a=d then 1 else 0)*(if b=c then 1 else 0))

lemma C6a_split (x : EuclideanSpace ℝ (Fin 8)) (p : T6k) :
    TestBCSplit.C6a x p = C6a1 x p + C6a2 x p := by
  simp only [TestBCSplit.C6a, C6a1, C6a2]; ring

lemma C6b_split (x : EuclideanSpace ℝ (Fin 8)) (p : T6k) :
    TestBCSplit.C6b x p = C6b1 x p + C6b2 x p + C6b3 x p := by
  simp only [TestBCSplit.C6b, C6b1, C6b2, C6b3]; ring

/-! ## C6a*C6a block: C6a1*C6a1 + 2*C6a1*C6a2 + C6a2*C6a2 = 1800*s² -/

set_option maxHeartbeats 4000000000 in
lemma sum_C6a1_C6a1 (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, C6a1 x p * C6a1 y p =
    540 * (@inner ℝ _ _ x y) ^ 2 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [C6a1]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 400000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 400000000 }) only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have rr : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  simp_rw [rr]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]
  simp_rw [← hs]
  ring

set_option maxHeartbeats 4000000000 in
lemma sum_C6a1_C6a2 (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, C6a1 x p * C6a2 y p =
    180 * (@inner ℝ _ _ x y) ^ 2 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [C6a1, C6a2]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 400000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 400000000 }) only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have rr : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  simp_rw [rr]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]
  simp_rw [← hs]
  ring

set_option maxHeartbeats 4000000000 in
lemma sum_C6a2_C6a2 (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, C6a2 x p * C6a2 y p =
    900 * (@inner ℝ _ _ x y) ^ 2 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [C6a2]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 400000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 400000000 }) only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have rr : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  simp_rw [rr]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul, ← hs]
  ring

lemma sum_C6a_C6a (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, TestBCSplit.C6a x p * TestBCSplit.C6a y p =
    1800 * (@inner ℝ _ _ x y) ^ 2 := by
  have h11 := sum_C6a1_C6a1 x y hx hy
  have h12 := sum_C6a1_C6a2 x y hx hy
  have h21 : ∑ p : T6k, C6a2 x p * C6a1 y p = 180 * (@inner ℝ _ _ x y) ^ 2 := by
    simp_rw [show ∀ p, C6a2 x p * C6a1 y p = C6a1 y p * C6a2 x p from fun p => mul_comm _ _]
    have h := sum_C6a1_C6a2 y x hy hx; rw [real_inner_comm] at h; exact h
  have h22 := sum_C6a2_C6a2 x y hx hy
  calc ∑ p : T6k, TestBCSplit.C6a x p * TestBCSplit.C6a y p
      = ∑ p, (C6a1 x p + C6a2 x p) * (C6a1 y p + C6a2 y p) := by
        congr 1; ext p; rw [C6a_split x p, C6a_split y p]
    _ = (∑ p, C6a1 x p * C6a1 y p) + (∑ p, C6a1 x p * C6a2 y p)
        + (∑ p, C6a2 x p * C6a1 y p) + (∑ p, C6a2 x p * C6a2 y p) := by
        simp [mul_add, add_mul, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]
    _ = 1800 * (@inner ℝ _ _ x y) ^ 2 := by rw [h11, h12, h21, h22]; ring

/-! ## Remaining sub-lemmas (C6a*C6b, C6b*C6b) -/

set_option maxHeartbeats 4000000000 in
lemma sum_C6a1_C6b1 (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, C6a1 x p * C6b1 y p =
    128 * (@inner ℝ _ _ x y) ^ 2 + 24 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [C6a1, C6b1]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 400000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 400000000 }) only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have rr : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  simp_rw [rr]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  have rr2 : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp b * y.ofLp a) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  simp_rw [rr2, ← Finset.mul_sum]
  try simp_rw [← Finset.sum_mul]
  simp_rw [← hs, hxn, hyn, mul_one]
  ring

set_option maxHeartbeats 4000000000 in
lemma sum_C6a1_C6b2 (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, C6a1 x p * C6b2 y p =
    102 * (@inner ℝ _ _ x y) ^ 2 + 36 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [C6a1, C6b2]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 400000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 400000000 }) only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have rr : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  simp_rw [rr]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  have rr2 : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp b * y.ofLp a) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  simp_rw [rr2, ← Finset.mul_sum]
  try simp_rw [← Finset.sum_mul]
  simp_rw [← hs, hxn, hyn, mul_one]
  ring

set_option maxHeartbeats 4000000000 in
lemma sum_C6a1_C6b3 (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, C6a1 x p * C6b3 y p =
    58 * (@inner ℝ _ _ x y) ^ 2 + 84 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [C6a1, C6b3]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 400000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 400000000 }) only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have rr : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  simp_rw [rr]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  have rr2 : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp b * y.ofLp a) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  simp_rw [rr2, ← Finset.mul_sum]
  try simp_rw [← Finset.sum_mul]
  simp_rw [← hs, hxn, hyn, mul_one]
  ring

set_option maxHeartbeats 4000000000 in
lemma sum_C6a2_C6b1 (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, C6a2 x p * C6b1 y p =
    88 * (@inner ℝ _ _ x y) ^ 2 + 84 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [C6a2, C6b1]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 400000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 400000000 }) only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have rr : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  simp_rw [rr]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  have rr2 : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp b * y.ofLp a) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  simp_rw [rr2, ← Finset.mul_sum]
  try simp_rw [← Finset.sum_mul]
  simp_rw [← hs, hxn, hyn, mul_one]
  ring

set_option maxHeartbeats 4000000000 in
lemma sum_C6a2_C6b2 (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, C6a2 x p * C6b2 y p =
    114 * (@inner ℝ _ _ x y) ^ 2 + 72 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [C6a2, C6b2]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 400000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 400000000 }) only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have rr : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  simp_rw [rr]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  have rr2 : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp b * y.ofLp a) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  simp_rw [rr2, ← Finset.mul_sum]
  try simp_rw [← Finset.sum_mul]
  simp_rw [← hs, hxn, hyn, mul_one]
  ring

set_option maxHeartbeats 4000000000 in
lemma sum_C6a2_C6b3 (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, C6a2 x p * C6b3 y p =
    230 * (@inner ℝ _ _ x y) ^ 2 + 60 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [C6a2, C6b3]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 400000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 400000000 }) only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have rr : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  simp_rw [rr]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  have rr2 : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp b * y.ofLp a) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  simp_rw [rr2, ← Finset.mul_sum]
  try simp_rw [← Finset.sum_mul]
  simp_rw [← hs, hxn, hyn, mul_one]
  ring

lemma sum_C6a_C6b (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, TestBCSplit.C6a x p * TestBCSplit.C6b y p =
    720 * (@inner ℝ _ _ x y) ^ 2 + 360 := by
  have h1 := sum_C6a1_C6b1 x y hx hy
  have h2 := sum_C6a1_C6b2 x y hx hy
  have h3 := sum_C6a1_C6b3 x y hx hy
  have h4 := sum_C6a2_C6b1 x y hx hy
  have h5 := sum_C6a2_C6b2 x y hx hy
  have h6 := sum_C6a2_C6b3 x y hx hy
  calc ∑ p : T6k, TestBCSplit.C6a x p * TestBCSplit.C6b y p
      = ∑ p, (C6a1 x p + C6a2 x p) * (C6b1 y p + C6b2 y p + C6b3 y p) := by
        congr 1; ext p; rw [C6a_split x p, C6b_split y p]
    _ = (∑ p, C6a1 x p * C6b1 y p) + (∑ p, C6a1 x p * C6b2 y p)
        + (∑ p, C6a1 x p * C6b3 y p) + (∑ p, C6a2 x p * C6b1 y p)
        + (∑ p, C6a2 x p * C6b2 y p) + (∑ p, C6a2 x p * C6b3 y p) := by
        simp [mul_add, add_mul, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]
    _ = 720 * (@inner ℝ _ _ x y) ^ 2 + 360 := by rw [h1, h2, h3, h4, h5, h6]; ring

lemma sum_C6b_C6a (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, TestBCSplit.C6b x p * TestBCSplit.C6a y p =
    720 * (@inner ℝ _ _ x y) ^ 2 + 360 := by
  simp_rw [show ∀ p, TestBCSplit.C6b x p * TestBCSplit.C6a y p =
    TestBCSplit.C6a y p * TestBCSplit.C6b x p from fun p => mul_comm _ _]
  have h := sum_C6a_C6b y x hy hx; rw [real_inner_comm] at h; exact h

set_option maxHeartbeats 4000000000 in
lemma sum_C6b1_C6b1 (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, C6b1 x p * C6b1 y p =
    900 * (@inner ℝ _ _ x y) ^ 2 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [C6b1]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 400000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 400000000 }) only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have rr : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  simp_rw [rr]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  have rs : ∀ a : Fin 8, s * x.ofLp a * y.ofLp a = s * (x.ofLp a * y.ofLp a) :=
    fun a => mul_assoc s (x.ofLp a) (y.ofLp a)
  try simp_rw [rs]
  simp_rw [← Finset.mul_sum]
  try simp_rw [← Finset.sum_mul]
  simp_rw [← hs]
  have h_s_sum : ∑ a : Fin 8, s * (x.ofLp a * y.ofLp a) = s ^ 2 := by
    simp_rw [← Finset.mul_sum, ← hs]; ring
  simp only [h_s_sum]; ring

set_option maxHeartbeats 4000000000 in
lemma sum_C6b1_C6b2 (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, C6b1 x p * C6b2 y p =
    218 * (@inner ℝ _ _ x y) ^ 2 + 24 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [C6b1, C6b2]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 400000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 400000000 }) only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have rr : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  simp_rw [rr]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  have rr2 : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp b * y.ofLp a) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  have rr3 : ∀ a b : Fin 8, x.ofLp b * x.ofLp a * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  have rr4 : ∀ a b : Fin 8, x.ofLp b * x.ofLp a * (y.ofLp b * y.ofLp a) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  try simp_rw [rr2]
  try simp_rw [rr3]
  try simp_rw [rr4]
  have rs : ∀ a : Fin 8, s * x.ofLp a * y.ofLp a = s * (x.ofLp a * y.ofLp a) := by
    intros; ring
  have sq_rw : ∀ a : Fin 8, y.ofLp a ^ 2 = y.ofLp a * y.ofLp a := by intros; ring
  try simp_rw [rs]
  try simp_rw [sq_rw]
  simp_rw [← Finset.mul_sum]
  try simp_rw [← Finset.sum_mul]
  simp_rw [← hs, hxn, hyn, mul_one]
  have h_s_sum : ∑ a : Fin 8, s * (x.ofLp a * y.ofLp a) = s ^ 2 := by
    simp_rw [← Finset.mul_sum, ← hs]; ring
  have h_y_sq : ∑ a : Fin 8, 1 * (y.ofLp a * y.ofLp a) = 1 := by
    simp_rw [one_mul]; exact hyn
  simp only [h_s_sum, h_y_sq]; ring

set_option maxHeartbeats 4000000000 in
lemma sum_C6b1_C6b3 (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, C6b1 x p * C6b3 y p =
    178 * (@inner ℝ _ _ x y) ^ 2 + 84 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [C6b1, C6b3]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 400000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 400000000 }) only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have rr : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  simp_rw [rr]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  have rr2 : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp b * y.ofLp a) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  have rr3 : ∀ a b : Fin 8, x.ofLp b * x.ofLp a * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  have rr4 : ∀ a b : Fin 8, x.ofLp b * x.ofLp a * (y.ofLp b * y.ofLp a) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  try simp_rw [rr2]
  try simp_rw [rr3]
  try simp_rw [rr4]
  have rs : ∀ a : Fin 8, s * x.ofLp a * y.ofLp a = s * (x.ofLp a * y.ofLp a) := by
    intros; ring
  have sq_rw : ∀ a : Fin 8, y.ofLp a ^ 2 = y.ofLp a * y.ofLp a := by intros; ring
  try simp_rw [rs]
  try simp_rw [sq_rw]
  simp_rw [← Finset.mul_sum]
  try simp_rw [← Finset.sum_mul]
  simp_rw [← hs, hxn, hyn, mul_one]
  have h_s_sum : ∑ a : Fin 8, s * (x.ofLp a * y.ofLp a) = s ^ 2 := by
    simp_rw [← Finset.mul_sum, ← hs]; ring
  have h_y_sq : ∑ a : Fin 8, 1 * (y.ofLp a * y.ofLp a) = 1 := by
    simp_rw [one_mul]; exact hyn
  simp only [h_s_sum, h_y_sq]; ring

set_option maxHeartbeats 4000000000 in
lemma sum_C6b2_C6b2 (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, C6b2 x p * C6b2 y p =
    796 * (@inner ℝ _ _ x y) ^ 2 + 48 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [C6b2]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 400000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 400000000 }) only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have rr : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  simp_rw [rr]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  have rr2 : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp b * y.ofLp a) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  have rr3 : ∀ a b : Fin 8, x.ofLp b * x.ofLp a * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  have rr4 : ∀ a b : Fin 8, x.ofLp b * x.ofLp a * (y.ofLp b * y.ofLp a) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  try simp_rw [rr2]
  try simp_rw [rr3]
  try simp_rw [rr4]
  have rs : ∀ a : Fin 8, s * x.ofLp a * y.ofLp a = s * (x.ofLp a * y.ofLp a) := by
    intros; ring
  have sq_rw : ∀ a : Fin 8, y.ofLp a ^ 2 = y.ofLp a * y.ofLp a := by intros; ring
  try simp_rw [rs]
  try simp_rw [sq_rw]
  simp_rw [← Finset.mul_sum]
  try simp_rw [← Finset.sum_mul]
  simp_rw [← hs, hxn, hyn, mul_one]
  have h_s_sum : ∑ a : Fin 8, s * (x.ofLp a * y.ofLp a) = s ^ 2 := by
    simp_rw [← Finset.mul_sum, ← hs]; ring
  have h_y_sq : ∑ a : Fin 8, 1 * (y.ofLp a * y.ofLp a) = 1 := by
    simp_rw [one_mul]; exact hyn
  simp only [h_s_sum, h_y_sq]; ring

set_option maxHeartbeats 4000000000 in
lemma sum_C6b2_C6b3 (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, C6b2 x p * C6b3 y p =
    282 * (@inner ℝ _ _ x y) ^ 2 + 36 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [C6b2, C6b3]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 400000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 400000000 }) only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 400000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 400000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have rr : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  simp_rw [rr]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  have rr2 : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp b * y.ofLp a) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  have rr3 : ∀ a b : Fin 8, x.ofLp b * x.ofLp a * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  have rr4 : ∀ a b : Fin 8, x.ofLp b * x.ofLp a * (y.ofLp b * y.ofLp a) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  try simp_rw [rr2]
  try simp_rw [rr3]
  try simp_rw [rr4]
  have rs : ∀ a : Fin 8, s * x.ofLp a * y.ofLp a = s * (x.ofLp a * y.ofLp a) := by
    intros; ring
  have sq_rw : ∀ a : Fin 8, y.ofLp a ^ 2 = y.ofLp a * y.ofLp a := by intros; ring
  try simp_rw [rs]
  try simp_rw [sq_rw]
  simp_rw [← Finset.mul_sum]
  try simp_rw [← Finset.sum_mul]
  simp_rw [← hs, hxn, hyn, mul_one]
  have h_s_sum : ∑ a : Fin 8, s * (x.ofLp a * y.ofLp a) = s ^ 2 := by
    simp_rw [← Finset.mul_sum, ← hs]; ring
  have h_y_sq : ∑ a : Fin 8, 1 * (y.ofLp a * y.ofLp a) = 1 := by
    simp_rw [one_mul]; exact hyn
  simp only [h_s_sum, h_y_sq]; ring

set_option maxHeartbeats 4000000000 in
lemma sum_C6b3_C6b3 (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, C6b3 x p * C6b3 y p =
    1268 * (@inner ℝ _ _ x y) ^ 2 + 24 := by
  set s := @inner ℝ _ _ x y
  have hs : s = ∑ a : Fin 8, x.ofLp a * y.ofLp a := inner_ofLp x y
  have hxn := ofLp_norm_sq x hx
  have hyn := ofLp_norm_sq y hy
  simp only [C6b3]
  simp_rw [Fintype.sum_prod_type]
  simp (config := { maxSteps := 800000000 }) only [add_mul, mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 800000000 }) only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul]
  simp (config := { maxSteps := 800000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 800000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 800000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw (config := { maxSteps := 800000000 }) [sum_ite_prop_zero]
  simp (config := { maxSteps := 800000000 }) only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have rr : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  simp_rw [rr]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  have rr2 : ∀ a b : Fin 8, x.ofLp a * x.ofLp b * (y.ofLp b * y.ofLp a) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  have rr3 : ∀ a b : Fin 8, x.ofLp b * x.ofLp a * (y.ofLp a * y.ofLp b) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  have rr4 : ∀ a b : Fin 8, x.ofLp b * x.ofLp a * (y.ofLp b * y.ofLp a) =
      (x.ofLp a * y.ofLp a) * (x.ofLp b * y.ofLp b) := by intros; ring
  try simp_rw [rr2]
  try simp_rw [rr3]
  try simp_rw [rr4]
  have rs : ∀ a : Fin 8, s * x.ofLp a * y.ofLp a = s * (x.ofLp a * y.ofLp a) := by
    intros; ring
  have sq_rw : ∀ a : Fin 8, y.ofLp a ^ 2 = y.ofLp a * y.ofLp a := by intros; ring
  try simp_rw [rs]
  try simp_rw [sq_rw]
  simp_rw [← Finset.mul_sum]
  try simp_rw [← Finset.sum_mul]
  simp_rw [← hs, hxn, hyn, mul_one]
  have h_s_sum : ∑ a : Fin 8, s * (x.ofLp a * y.ofLp a) = s ^ 2 := by
    simp_rw [← Finset.mul_sum, ← hs]; ring
  have h_y_sq : ∑ a : Fin 8, 1 * (y.ofLp a * y.ofLp a) = 1 := by
    simp_rw [one_mul]; exact hyn
  simp only [h_s_sum, h_y_sq]; ring

lemma sum_C6b_C6b (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ p : T6k, TestBCSplit.C6b x p * TestBCSplit.C6b y p =
    4320 * (@inner ℝ _ _ x y) ^ 2 + 360 := by
  have h11 := sum_C6b1_C6b1 x y hx hy
  have h12 := sum_C6b1_C6b2 x y hx hy
  have h13 := sum_C6b1_C6b3 x y hx hy
  have h21 : ∑ p : T6k, C6b2 x p * C6b1 y p = 218 * (@inner ℝ _ _ x y) ^ 2 + 24 := by
    simp_rw [show ∀ p, C6b2 x p * C6b1 y p = C6b1 y p * C6b2 x p from fun p => mul_comm _ _]
    have h := sum_C6b1_C6b2 y x hy hx; rw [real_inner_comm] at h; exact h
  have h22 := sum_C6b2_C6b2 x y hx hy
  have h23 := sum_C6b2_C6b3 x y hx hy
  have h31 : ∑ p : T6k, C6b3 x p * C6b1 y p = 178 * (@inner ℝ _ _ x y) ^ 2 + 84 := by
    simp_rw [show ∀ p, C6b3 x p * C6b1 y p = C6b1 y p * C6b3 x p from fun p => mul_comm _ _]
    have h := sum_C6b1_C6b3 y x hy hx; rw [real_inner_comm] at h; exact h
  have h32 : ∑ p : T6k, C6b3 x p * C6b2 y p = 282 * (@inner ℝ _ _ x y) ^ 2 + 36 := by
    simp_rw [show ∀ p, C6b3 x p * C6b2 y p = C6b2 y p * C6b3 x p from fun p => mul_comm _ _]
    have h := sum_C6b2_C6b3 y x hy hx; rw [real_inner_comm] at h; exact h
  have h33 := sum_C6b3_C6b3 x y hx hy
  calc ∑ p : T6k, TestBCSplit.C6b x p * TestBCSplit.C6b y p
      = ∑ p, (C6b1 x p + C6b2 x p + C6b3 x p) * (C6b1 y p + C6b2 y p + C6b3 y p) := by
        congr 1; ext p; rw [C6b_split x p, C6b_split y p]
    _ = (∑ p, C6b1 x p * C6b1 y p) + (∑ p, C6b1 x p * C6b2 y p) + (∑ p, C6b1 x p * C6b3 y p)
        + (∑ p, C6b2 x p * C6b1 y p) + (∑ p, C6b2 x p * C6b2 y p) + (∑ p, C6b2 x p * C6b3 y p)
        + (∑ p, C6b3 x p * C6b1 y p) + (∑ p, C6b3 x p * C6b2 y p) + (∑ p, C6b3 x p * C6b3 y p) := by
        simp [mul_add, add_mul, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]
    _ = 4320 * (@inner ℝ _ _ x y) ^ 2 + 360 := by
        rw [h11, h12, h13, h21, h22, h23, h31, h32, h33]; ring

end TestCCSplit
