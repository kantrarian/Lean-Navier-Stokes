import KissingNumber.Gegenbauer
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators RealInnerProductSpace
open Real Finset

noncomputable section

namespace PSD6Defs

/-- Type alias for 6-tuples used in k=6 feature maps. -/
abbrev T6 := Fin 8 × Fin 8 × Fin 8 × Fin 8 × Fin 8 × Fin 8

lemma ofLp_norm_sq (x : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) :
    ∑ a : Fin 8, x.ofLp a * x.ofLp a = 1 := by
  have h1 : @inner ℝ _ _ x x = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have h2 : @inner ℝ _ _ x x = ∑ a : Fin 8, x.ofLp a * x.ofLp a := by
    rw [PiLp.inner_apply]; congr 1
  linarith

lemma inner_ofLp (x y : EuclideanSpace ℝ (Fin 8)) :
    @inner ℝ _ _ x y = ∑ a : Fin 8, x.ofLp a * y.ofLp a := by
  rw [PiLp.inner_apply]; congr 1; ext a
  simp [RCLike.inner_apply, conj_trivial, mul_comm]

lemma sum_ite_const_zero {f : Fin 8 → ℝ} :
    ∀ a : Fin 8, ∑ b : Fin 8, (if a = b then f b else 0) = f a :=
  fun a => by simp [Finset.sum_ite_eq, Finset.mem_univ]

lemma sum_ite_prop_zero {p : Prop} [Decidable p] (f : Fin 8 → ℝ) :
    ∑ x : Fin 8, (if p then f x else 0) = if p then ∑ x, f x else 0 := by
  split_ifs <;> simp

lemma factor2 (f g : Fin 8 → ℝ) :
    ∑ a : Fin 8, ∑ b : Fin 8, f a * g b =
    (∑ a, f a) * (∑ b, g b) := by
  rw [Finset.sum_mul]; congr 1; ext a; rw [← Finset.mul_sum]

lemma factor3 (f g h : Fin 8 → ℝ) :
    ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, f a * g b * h c =
    (∑ a, f a) * (∑ b, g b) * (∑ c, h c) := by
  simp_rw [← Finset.mul_sum, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]

lemma factor4 (f g h j : Fin 8 → ℝ) :
    ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, ∑ d : Fin 8, f a * g b * h c * j d =
    (∑ a, f a) * (∑ b, g b) * (∑ c, h c) * (∑ d, j d) := by
  simp_rw [← Finset.mul_sum, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]

-- factor4 permutation variants: handle sums where body factors depend on
-- variables in non-standard order (e.g., (a,c,b,d) instead of (a,b,c,d))
lemma factor4_acbd (f g h j : Fin 8 → ℝ) :
    ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, ∑ d : Fin 8, f a * h c * g b * j d =
    (∑ a, f a) * (∑ b, g b) * (∑ c, h c) * (∑ d, j d) := by
  simp_rw [show ∀ a b c d, f a * h c * g b * j d = f a * g b * h c * j d from by intros; ring]
  exact factor4 f g h j

lemma factor4_adbc (f g h j : Fin 8 → ℝ) :
    ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, ∑ d : Fin 8, f a * j d * g b * h c =
    (∑ a, f a) * (∑ b, g b) * (∑ c, h c) * (∑ d, j d) := by
  simp_rw [show ∀ a b c d, f a * j d * g b * h c = f a * g b * h c * j d from by intros; ring]
  exact factor4 f g h j

lemma factor4_bcad (f g h j : Fin 8 → ℝ) :
    ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, ∑ d : Fin 8, g b * h c * f a * j d =
    (∑ a, f a) * (∑ b, g b) * (∑ c, h c) * (∑ d, j d) := by
  simp_rw [show ∀ a b c d, g b * h c * f a * j d = f a * g b * h c * j d from by intros; ring]
  exact factor4 f g h j

lemma factor4_bdac (f g h j : Fin 8 → ℝ) :
    ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, ∑ d : Fin 8, g b * j d * f a * h c =
    (∑ a, f a) * (∑ b, g b) * (∑ c, h c) * (∑ d, j d) := by
  simp_rw [show ∀ a b c d, g b * j d * f a * h c = f a * g b * h c * j d from by intros; ring]
  exact factor4 f g h j

lemma factor4_cdab (f g h j : Fin 8 → ℝ) :
    ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, ∑ d : Fin 8, h c * j d * f a * g b =
    (∑ a, f a) * (∑ b, g b) * (∑ c, h c) * (∑ d, j d) := by
  simp_rw [show ∀ a b c d, h c * j d * f a * g b = f a * g b * h c * j d from by intros; ring]
  exact factor4 f g h j

lemma factor5 (f g h j k : Fin 8 → ℝ) :
    ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, ∑ d : Fin 8, ∑ e : Fin 8,
      f a * g b * h c * j d * k e =
    (∑ a, f a) * (∑ b, g b) * (∑ c, h c) * (∑ d, j d) * (∑ e, k e) := by
  simp_rw [← Finset.mul_sum, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]

lemma factor6 (f g h j k l : Fin 8 → ℝ) :
    ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, ∑ d : Fin 8, ∑ e : Fin 8, ∑ t : Fin 8,
      f a * g b * h c * j d * k e * l t =
    (∑ a, f a) * (∑ b, g b) * (∑ c, h c) * (∑ d, j d) * (∑ e, k e) * (∑ t, l t) := by
  simp_rw [← Finset.mul_sum, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]

def A6 (x : EuclideanSpace ℝ (Fin 8)) (p : T6) : ℝ :=
  x p.1 * x p.2.1 * x p.2.2.1 * x p.2.2.2.1 * x p.2.2.2.2.1 * x p.2.2.2.2.2

def B6 (x : EuclideanSpace ℝ (Fin 8)) (p : T6) : ℝ :=
  let a := p.1; let b := p.2.1; let c := p.2.2.1
  let d := p.2.2.2.1; let e := p.2.2.2.2.1; let f := p.2.2.2.2.2
  (if a = b then 1 else 0) * x c * x d * x e * x f
  + (if a = c then 1 else 0) * x b * x d * x e * x f
  + (if a = d then 1 else 0) * x b * x c * x e * x f
  + (if a = e then 1 else 0) * x b * x c * x d * x f
  + (if a = f then 1 else 0) * x b * x c * x d * x e
  + (if b = c then 1 else 0) * x a * x d * x e * x f
  + (if b = d then 1 else 0) * x a * x c * x e * x f
  + (if b = e then 1 else 0) * x a * x c * x d * x f
  + (if b = f then 1 else 0) * x a * x c * x d * x e
  + (if c = d then 1 else 0) * x a * x b * x e * x f
  + (if c = e then 1 else 0) * x a * x b * x d * x f
  + (if c = f then 1 else 0) * x a * x b * x d * x e
  + (if d = e then 1 else 0) * x a * x b * x c * x f
  + (if d = f then 1 else 0) * x a * x b * x c * x e
  + (if e = f then 1 else 0) * x a * x b * x c * x d

def C6 (x : EuclideanSpace ℝ (Fin 8)) (p : T6) : ℝ :=
  let a := p.1; let b := p.2.1; let c := p.2.2.1
  let d := p.2.2.2.1; let e := p.2.2.2.2.1; let f := p.2.2.2.2.2
  x a * x b * ((if c=d then 1 else 0)*(if e=f then 1 else 0) + (if c=e then 1 else 0)*(if d=f then 1 else 0) + (if c=f then 1 else 0)*(if d=e then 1 else 0))
  + x a * x c * ((if b=d then 1 else 0)*(if e=f then 1 else 0) + (if b=e then 1 else 0)*(if d=f then 1 else 0) + (if b=f then 1 else 0)*(if d=e then 1 else 0))
  + x a * x d * ((if b=c then 1 else 0)*(if e=f then 1 else 0) + (if b=e then 1 else 0)*(if c=f then 1 else 0) + (if b=f then 1 else 0)*(if c=e then 1 else 0))
  + x a * x e * ((if b=c then 1 else 0)*(if d=f then 1 else 0) + (if b=d then 1 else 0)*(if c=f then 1 else 0) + (if b=f then 1 else 0)*(if c=d then 1 else 0))
  + x a * x f * ((if b=c then 1 else 0)*(if d=e then 1 else 0) + (if b=d then 1 else 0)*(if c=e then 1 else 0) + (if b=e then 1 else 0)*(if c=d then 1 else 0))
  + x b * x c * ((if a=d then 1 else 0)*(if e=f then 1 else 0) + (if a=e then 1 else 0)*(if d=f then 1 else 0) + (if a=f then 1 else 0)*(if d=e then 1 else 0))
  + x b * x d * ((if a=c then 1 else 0)*(if e=f then 1 else 0) + (if a=e then 1 else 0)*(if c=f then 1 else 0) + (if a=f then 1 else 0)*(if c=e then 1 else 0))
  + x b * x e * ((if a=c then 1 else 0)*(if d=f then 1 else 0) + (if a=d then 1 else 0)*(if c=f then 1 else 0) + (if a=f then 1 else 0)*(if c=d then 1 else 0))
  + x b * x f * ((if a=c then 1 else 0)*(if d=e then 1 else 0) + (if a=d then 1 else 0)*(if c=e then 1 else 0) + (if a=e then 1 else 0)*(if c=d then 1 else 0))
  + x c * x d * ((if a=b then 1 else 0)*(if e=f then 1 else 0) + (if a=e then 1 else 0)*(if b=f then 1 else 0) + (if a=f then 1 else 0)*(if b=e then 1 else 0))
  + x c * x e * ((if a=b then 1 else 0)*(if d=f then 1 else 0) + (if a=d then 1 else 0)*(if b=f then 1 else 0) + (if a=f then 1 else 0)*(if b=d then 1 else 0))
  + x c * x f * ((if a=b then 1 else 0)*(if d=e then 1 else 0) + (if a=d then 1 else 0)*(if b=e then 1 else 0) + (if a=e then 1 else 0)*(if b=d then 1 else 0))
  + x d * x e * ((if a=b then 1 else 0)*(if c=f then 1 else 0) + (if a=c then 1 else 0)*(if b=f then 1 else 0) + (if a=f then 1 else 0)*(if b=c then 1 else 0))
  + x d * x f * ((if a=b then 1 else 0)*(if c=e then 1 else 0) + (if a=c then 1 else 0)*(if b=e then 1 else 0) + (if a=e then 1 else 0)*(if b=c then 1 else 0))
  + x e * x f * ((if a=b then 1 else 0)*(if c=d then 1 else 0) + (if a=c then 1 else 0)*(if b=d then 1 else 0) + (if a=d then 1 else 0)*(if b=c then 1 else 0))

def D6 (_x : EuclideanSpace ℝ (Fin 8)) (p : T6) : ℝ :=
  let a := p.1; let b := p.2.1; let c := p.2.2.1
  let d := p.2.2.2.1; let e := p.2.2.2.2.1; let f := p.2.2.2.2.2
  (if a=b then 1 else 0) * ((if c=d then 1 else 0)*(if e=f then 1 else 0) + (if c=e then 1 else 0)*(if d=f then 1 else 0) + (if c=f then 1 else 0)*(if d=e then 1 else 0))
  + (if a=c then 1 else 0) * ((if b=d then 1 else 0)*(if e=f then 1 else 0) + (if b=e then 1 else 0)*(if d=f then 1 else 0) + (if b=f then 1 else 0)*(if d=e then 1 else 0))
  + (if a=d then 1 else 0) * ((if b=c then 1 else 0)*(if e=f then 1 else 0) + (if b=e then 1 else 0)*(if c=f then 1 else 0) + (if b=f then 1 else 0)*(if c=e then 1 else 0))
  + (if a=e then 1 else 0) * ((if b=c then 1 else 0)*(if d=f then 1 else 0) + (if b=d then 1 else 0)*(if c=f then 1 else 0) + (if b=f then 1 else 0)*(if c=d then 1 else 0))
  + (if a=f then 1 else 0) * ((if b=c then 1 else 0)*(if d=e then 1 else 0) + (if b=d then 1 else 0)*(if c=e then 1 else 0) + (if b=e then 1 else 0)*(if c=d then 1 else 0))

def phi6 (x : EuclideanSpace ℝ (Fin 8)) (p : T6) : ℝ :=
  A6 x p - (1 : ℝ) / 16 * B6 x p + (1 : ℝ) / 224 * C6 x p - (1 : ℝ) / 2688 * D6 x p

lemma phi6_product (x y : EuclideanSpace ℝ (Fin 8)) (p : T6) :
    phi6 x p * phi6 y p =
    A6 x p * A6 y p
    - (1/16) * (A6 x p * B6 y p + B6 x p * A6 y p)
    + (1/224) * (A6 x p * C6 y p + C6 x p * A6 y p)
    - (1/2688) * (A6 x p * D6 y p + D6 x p * A6 y p)
    + (1/256) * (B6 x p * B6 y p)
    - (1/3584) * (B6 x p * C6 y p + C6 x p * B6 y p)
    + (1/43008) * (B6 x p * D6 y p + D6 x p * B6 y p)
    + (1/50176) * (C6 x p * C6 y p)
    - (1/602112) * (C6 x p * D6 y p + D6 x p * C6 y p)
    + (1/7225344) * (D6 x p * D6 y p) := by
  simp only [phi6]; ring

end PSD6Defs
