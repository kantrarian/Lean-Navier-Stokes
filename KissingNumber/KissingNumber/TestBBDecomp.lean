import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open scoped BigOperators
open Finset

noncomputable section

private lemma ofLp_norm_sq' (x : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) :
    ∑ a : Fin 8, x.ofLp a * x.ofLp a = 1 := by
  have h1 : @inner ℝ _ _ x x = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have h2 : @inner ℝ _ _ x x = ∑ a : Fin 8, x.ofLp a * x.ofLp a := by
    rw [PiLp.inner_apply]; congr 1
  linarith

private lemma inner_ofLp' (x y : EuclideanSpace ℝ (Fin 8)) :
    @inner ℝ _ _ x y = ∑ a : Fin 8, x.ofLp a * y.ofLp a := by
  rw [PiLp.inner_apply]; congr 1; ext a
  simp [RCLike.inner_apply, conj_trivial, mul_comm]

private lemma sum_ite_prop_zero' {p : Prop} [Decidable p] (f : Fin 8 → ℝ) :
    ∑ x : Fin 8, (if p then f x else 0) = if p then ∑ x, f x else 0 := by
  split_ifs <;> simp

private lemma factor4' (f g h j : Fin 8 → ℝ) :
    ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, ∑ d : Fin 8, f a * g b * h c * j d =
    (∑ a, f a) * (∑ b, g b) * (∑ c, h c) * (∑ d, j d) := by
  simp_rw [← Finset.mul_sum, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]

-- Test 1: Same-pair cross-term (pair {a,b} x pair {a,b})
-- After collapse: 5-fold sum, product doesn't depend on first variable
-- Result: 8 * s^4
set_option maxHeartbeats 4000000 in
example (x y : EuclideanSpace ℝ (Fin 8)) :
    ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, ∑ d : Fin 8, ∑ e : Fin 8, ∑ f : Fin 8,
      ((if a = b then (1:ℝ) else 0) * x.ofLp c * x.ofLp d * x.ofLp e * x.ofLp f) *
      ((if a = b then (1:ℝ) else 0) * y.ofLp c * y.ofLp d * y.ofLp e * y.ofLp f) =
    8 * (∑ a : Fin 8, x.ofLp a * y.ofLp a) ^ 4 := by
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, one_mul]
  simp_rw [sum_ite_prop_zero']
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Goal: ∑_a ∑_c ∑_d ∑_e ∑_f, x c * x d * x e * x f * (y c * y d * y e * y f) = 8 * s^4
  -- The product doesn't depend on a, so ∑_a (...) = 8 * (...)
  have rm : ∀ c d e f : Fin 8, x.ofLp c * x.ofLp d * x.ofLp e * x.ofLp f *
    (y.ofLp c * y.ofLp d * y.ofLp e * y.ofLp f) =
    (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) * (x.ofLp f * y.ofLp f) := by
    intros; ring
  simp_rw [rm, factor4']
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring

-- Test 2: Overlap cross-term (pair {a,b} x pair {a,c})
-- Result: s^4
set_option maxHeartbeats 4000000 in
example (x y : EuclideanSpace ℝ (Fin 8)) :
    ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, ∑ d : Fin 8, ∑ e : Fin 8, ∑ f : Fin 8,
      ((if a = b then (1:ℝ) else 0) * x.ofLp c * x.ofLp d * x.ofLp e * x.ofLp f) *
      ((if a = c then (1:ℝ) else 0) * y.ofLp b * y.ofLp d * y.ofLp e * y.ofLp f) =
    (∑ a : Fin 8, x.ofLp a * y.ofLp a) ^ 4 := by
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, one_mul]
  simp_rw [sum_ite_prop_zero']
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have rr : ∀ a d e f : Fin 8, x.ofLp a * x.ofLp d * x.ofLp e * x.ofLp f *
    (y.ofLp a * y.ofLp d * y.ofLp e * y.ofLp f) =
    (x.ofLp a * y.ofLp a) * (x.ofLp d * y.ofLp d) * (x.ofLp e * y.ofLp e) * (x.ofLp f * y.ofLp f) := by
    intros; ring
  simp_rw [rr, factor4']
  ring

-- Test 3: Disjoint cross-term (pair {a,b} x pair {c,d})
-- Result: s^2 (using hxn and hyn)
set_option maxHeartbeats 4000000 in
example (x y : EuclideanSpace ℝ (Fin 8)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ a : Fin 8, ∑ b : Fin 8, ∑ c : Fin 8, ∑ d : Fin 8, ∑ e : Fin 8, ∑ f : Fin 8,
      ((if a = b then (1:ℝ) else 0) * x.ofLp c * x.ofLp d * x.ofLp e * x.ofLp f) *
      ((if c = d then (1:ℝ) else 0) * y.ofLp a * y.ofLp b * y.ofLp e * y.ofLp f) =
    (∑ a : Fin 8, x.ofLp a * y.ofLp a) ^ 2 := by
  have hxn := ofLp_norm_sq' x hx
  have hyn := ofLp_norm_sq' y hy
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, one_mul]
  simp_rw [sum_ite_prop_zero']
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- After first round: still has if x_1 = x_2. Need second round.
  simp_rw [sum_ite_prop_zero']
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Goal: ∑ x_1, ∑ x_2, ∑ x_3, ∑ x_4,
  --   x.ofLp x_2 * x.ofLp x_2 * x.ofLp x_3 * x.ofLp x_4 *
  --   (y.ofLp x_1 * y.ofLp x_1 * y.ofLp x_3 * y.ofLp x_4) = s^2
  have rd : ∀ a b c d : Fin 8,
    x.ofLp b * x.ofLp b * x.ofLp c * x.ofLp d * (y.ofLp a * y.ofLp a * y.ofLp c * y.ofLp d) =
    (y.ofLp a * y.ofLp a) * (x.ofLp b * x.ofLp b) * (x.ofLp c * y.ofLp c) * (x.ofLp d * y.ofLp d) := by
    intros; ring
  simp_rw [rd, factor4', hyn, hxn]
  ring

end
