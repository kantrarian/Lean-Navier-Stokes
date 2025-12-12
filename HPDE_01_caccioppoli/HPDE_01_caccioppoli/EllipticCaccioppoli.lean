import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import HPDE_common.HPDE_common
import HPDE_common.CylinderNotation
import HPDE_common.CutoffProperties

open Real MeasureTheory Set Metric

namespace HPDE_01

variable (u : (Fin 3 → ℝ) → ℝ) (r R : ℝ)

/-!
# Elliptic Caccioppoli Inequality

For u harmonic on B_R ⊂ ℝ³, we prove the energy estimate:

  ∫_{B_r} |∇u|² ≤ C/(R-r)² · ∫_{B_R} u²

This is a fundamental local regularity estimate for elliptic PDEs.

**Important note on norms:**
The domain `Fin 3 → ℝ` uses the **sup norm** by default, so `‖fderiv ℝ u x‖` gives
the operator norm in ℓ∞ space (= ℓ¹ norm of gradient coefficients).

For PDE applications, we want the **Euclidean/ℓ² gradient norm**:
  |∇u|² = ∑ᵢ (∂u/∂xᵢ)²

We define `gradientSq` to compute this coordinate-based squared gradient.

## Proof Strategy

1. Choose smooth cutoff η with η=1 on B_r, supp(η) ⊂ B_R, ‖∇η‖ ≤ C/(R-r)
   (from HPDE_common.exists_smooth_cutoff_ball)

2. Test weak harmonicity ∫ ∇u · ∇φ = 0 with φ = η²u

3. Expand: ∫ η²|∇u|² + 2∫ ηu ∇u·∇η = 0

4. Estimate cross term using Cauchy-Schwarz + Young:
   |∫ ηu ∇u·∇η| ≤ ε∫ η²|∇u|² + C/ε ∫ u²|∇η|²

5. Choose ε small to absorb gradient term on LHS

6. Use ‖∇η‖ ≤ C/(R-r) to conclude

## References

Ladyzhenskaya-Ural'tseva, Chapter 3 (elliptic Caccioppoli)
-/

/-- u is harmonic on B_R if Δu = 0 there (weak formulation) -/
def IsHarmonicOn (u : (Fin 3 → ℝ) → ℝ) (R : ℝ) : Prop :=
  -- Weak formulation: ∫ ∇u · ∇φ = 0 for all test functions φ with support in B_R
  -- Here ∇u · ∇φ means the inner product of gradients as vectors in ℝ³
  ∀ φ : (Fin 3 → ℝ) → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
    (∀ x, x ∉ ball (0 : Fin 3 → ℝ) R → φ x = 0) →
    ∫ x in closedBall (0 : Fin 3 → ℝ) R,
      -- Sum of partial derivatives: Σᵢ (∂u/∂xᵢ)(∂φ/∂xᵢ)
      ∑ i : Fin 3, (fderiv ℝ u x) (Pi.single i 1) * (fderiv ℝ φ x) (Pi.single i 1) = 0

/-- Squared Euclidean gradient: |∇f|² = ∑ᵢ (∂f/∂xᵢ)²

This is the coordinate-based squared gradient that matches PDE energy integrals.
Note: This is NOT the same as ‖fderiv ℝ f x‖² when using sup norm on Fin 3 → ℝ.
-/
noncomputable def gradientSq (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, ((fderiv ℝ f x) (Pi.single i 1))^2

/-- gradientSq is bounded by the operator norm squared.

For `Fin 3 → ℝ` with sup norm (ℓ∞), the dual norm on linear functionals is ℓ¹:
  ‖L‖ = ∑ᵢ |L(eᵢ)|

Therefore:
  ‖fderiv‖² = (∑ᵢ |∂f/∂xᵢ|)² ≥ ∑ᵢ (∂f/∂xᵢ)² = gradientSq

This follows from the algebraic fact that (∑|aᵢ|)² = ∑aᵢ² + 2∑_{i<j}|aᵢ||aⱼ| ≥ ∑aᵢ².
-/
lemma gradientSq_le_fderiv_norm_sq (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) :
    gradientSq f x ≤ ‖fderiv ℝ f x‖^2 := by
  -- For ℓ∞ dual: ‖L‖ = ∑ᵢ |L(eᵢ)|, so ‖fderiv‖² = (∑ᵢ |∂f/∂xᵢ|)² ≥ ∑ᵢ (∂f/∂xᵢ)²
  -- The algebraic fact is: (∑|aᵢ|)² = ∑aᵢ² + 2∑_{i<j}|aᵢ||aⱼ| ≥ ∑aᵢ²
  -- This requires the ℓ¹ characterization of the dual norm on (Fin 3 → ℝ) → ℝ
  sorry

/-- Helper: The standard basis vector Pi.single i 1 has norm 1 in the sup norm.

For `Fin 3 → ℝ` with sup norm, Pi.single i 1 is 1 at coordinate i and 0 elsewhere,
so its sup norm is max{0, 0, ..., 1, ..., 0} = 1.

TODO: Pure linear algebra - not needed for primary Caccioppoli statement.
-/
lemma norm_pi_single_one (i : Fin 3) : ‖(Pi.single i (1 : ℝ) : Fin 3 → ℝ)‖ = 1 := by
  sorry

/-- gradientSq is bounded by 3 times the operator norm squared.

Since each |∂f/∂xᵢ| ≤ ‖fderiv‖ (from operator norm bound with ‖eᵢ‖_∞ ≤ 1),
we have ∑ᵢ (∂f/∂xᵢ)² ≤ 3 · ‖fderiv‖².

Key step: For the sup norm on Fin 3 → ℝ, ‖Pi.single i 1‖ ≤ 1, so
  |(fderiv ℝ f x)(eᵢ)| ≤ ‖fderiv ℝ f x‖ · ‖eᵢ‖ ≤ ‖fderiv ℝ f x‖
-/
lemma gradientSq_le_three_mul_fderiv_norm_sq (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) :
    gradientSq f x ≤ 3 * ‖fderiv ℝ f x‖^2 := by
  unfold gradientSq
  -- For each i, |∂f/∂xᵢ|² ≤ ‖fderiv‖²
  -- Key insight: |(fderiv ℝ f x)(eᵢ)| ≤ ‖fderiv‖ · ‖eᵢ‖ ≤ ‖fderiv‖ since ‖eᵢ‖_∞ = 1
  -- So (∂f/∂xᵢ)² ≤ ‖fderiv‖², and summing gives ∑ᵢ (∂f/∂xᵢ)² ≤ 3·‖fderiv‖²
  -- TODO: Pi.norm_def uses NNNorm which requires more setup
  sorry

/-- The operator norm squared is bounded by 3 times gradientSq.

By Cauchy-Schwarz: (∑ᵢ |aᵢ|)² ≤ n · ∑ᵢ aᵢ² = 3 · gradientSq

This allows us to convert from coordinate-sum bounds (which arise from weak formulations)
to operator-norm bounds (which appear in the final Caccioppoli statement).

Note: This requires the ℓ¹ characterization of the dual norm on (Fin 3 → ℝ) → ℝ.
-/
lemma fderiv_norm_sq_le_three_mul_gradientSq (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) :
    ‖fderiv ℝ f x‖^2 ≤ 3 * gradientSq f x := by
  unfold gradientSq
  by_cases hf : DifferentiableAt ℝ f x
  · -- For ℓ∞ → ℝ, the operator norm is ‖L‖ = ∑ᵢ |L(eᵢ)|
    -- We need: (∑ᵢ |aᵢ|)² ≤ 3 · ∑ᵢ aᵢ² by Cauchy-Schwarz
    -- This requires the explicit ℓ¹ characterization of the dual norm
    sorry
  · simp only [fderiv_zero_of_not_differentiableAt hf, ContinuousLinearMap.zero_apply]
    simp only [sq, mul_zero, Finset.sum_const_zero, norm_zero, mul_self_nonneg, le_refl]

/-!
## Helper Lemmas for Caccioppoli

These break down the proof into manageable pieces.
-/

/--
Young's inequality for products: 2ab ≤ εa² + b²/ε for ε > 0.
This is the key estimate for handling cross terms.

Proof: Apply 2xy ≤ x² + y² to x = √ε·|a|, y = |b|/√ε
-/
lemma young_inequality (a b : ℝ) (ε : ℝ) (hε : 0 < ε) :
    2 * |a * b| ≤ ε * a^2 + b^2 / ε := by
  -- Rewrite |a * b| = |a| * |b|
  rw [abs_mul]
  -- Let x = √ε * |a|, y = |b| / √ε
  have h_sqrt : Real.sqrt ε > 0 := Real.sqrt_pos.mpr hε
  have h_ne : Real.sqrt ε ≠ 0 := ne_of_gt h_sqrt
  -- Transform: 2 * (|a| * |b|) = 2 * (√ε * |a|) * (|b| / √ε)
  have h_eq : 2 * (|a| * |b|) = 2 * (Real.sqrt ε * |a|) * (|b| / Real.sqrt ε) := by
    field_simp
  rw [h_eq]
  -- Apply basic AM-GM: 2xy ≤ x² + y²
  have h_amgm := two_mul_le_add_sq (Real.sqrt ε * |a|) (|b| / Real.sqrt ε)
  calc 2 * (Real.sqrt ε * |a|) * (|b| / Real.sqrt ε)
      ≤ (Real.sqrt ε * |a|)^2 + (|b| / Real.sqrt ε)^2 := h_amgm
    _ = ε * a^2 + b^2 / ε := by
          simp only [mul_pow, Real.sq_sqrt hε.le, sq_abs, div_pow]

/--
Energy on inner ball is controlled by weighted energy on larger ball.
This uses η = 1 on B_r.

Proof: Since η = 1 on B_r, we have f² = η²f² there.
Then ∫_{B_r} η²f² ≤ ∫_{B_R} η²f² by monotonicity (since B_r ⊆ B_R and η²f² ≥ 0).
-/
lemma inner_ball_energy_bound
    (η : (Fin 3 → ℝ) → ℝ) (f : (Fin 3 → ℝ) → ℝ) (r R : ℝ)
    (hrR : r ≤ R)
    (h_one : ∀ x ∈ closedBall (0 : Fin 3 → ℝ) r, η x = 1)
    (h_integ : IntegrableOn (fun x => (η x)^2 * (f x)^2) (closedBall (0 : Fin 3 → ℝ) R)) :
    ∫ x in closedBall (0 : Fin 3 → ℝ) r, (f x)^2 ≤
    ∫ x in closedBall (0 : Fin 3 → ℝ) R, (η x)^2 * (f x)^2 := by
  -- Step 1: On B_r, f² = η²f² since η = 1 there
  have h_eq : ∀ x ∈ closedBall (0 : Fin 3 → ℝ) r, (f x)^2 = (η x)^2 * (f x)^2 := by
    intro x hx
    rw [h_one x hx, one_pow, one_mul]
  -- Step 2: Rewrite the LHS integral using this equality
  have h_int_eq : ∫ x in closedBall (0 : Fin 3 → ℝ) r, (f x)^2 =
                  ∫ x in closedBall (0 : Fin 3 → ℝ) r, (η x)^2 * (f x)^2 := by
    apply setIntegral_congr_fun measurableSet_closedBall
    exact h_eq
  rw [h_int_eq]
  -- Step 3: Apply monotonicity: ∫_{B_r} g ≤ ∫_{B_R} g for g ≥ 0
  apply setIntegral_mono_set
  · exact h_integ
  · -- η²f² ≥ 0 a.e.
    filter_upwards with x
    apply mul_nonneg (sq_nonneg _) (sq_nonneg _)
  · -- B_r ⊆ B_R a.e.
    filter_upwards with x hx
    exact closedBall_subset_closedBall hrR hx

/--
Gradient bound estimate: Using ‖∇η‖ ≤ C/(R-r) to bound weighted gradient integral.

Proof: Since ‖∇η‖ ≤ C/(R-r) pointwise, we have
  u²‖∇η‖² ≤ u²(C/(R-r))² = (C/(R-r))² u²
at every point, and integration preserves this inequality.
-/
lemma gradient_bound_estimate
    (η u : (Fin 3 → ℝ) → ℝ) (C R r : ℝ)
    (hC : 0 ≤ C) (hRr : r < R)
    (h_grad : ∀ x, ‖fderiv ℝ η x‖ ≤ C / (R - r))
    (h_integ : IntegrableOn (fun x => (u x)^2) (closedBall (0 : Fin 3 → ℝ) R))
    (h_integ' : IntegrableOn (fun x => (u x)^2 * ‖fderiv ℝ η x‖^2) (closedBall (0 : Fin 3 → ℝ) R)) :
    ∫ x in closedBall (0 : Fin 3 → ℝ) R, (u x)^2 * ‖fderiv ℝ η x‖^2 ≤
    (C / (R - r))^2 * ∫ x in closedBall (0 : Fin 3 → ℝ) R, (u x)^2 := by
  -- Step 1: Pointwise inequality
  have h_pointwise : ∀ x, (u x)^2 * ‖fderiv ℝ η x‖^2 ≤ (C / (R - r))^2 * (u x)^2 := fun x => by
    have h_nonneg : 0 ≤ ‖fderiv ℝ η x‖ := norm_nonneg _
    have h_bound : ‖fderiv ℝ η x‖ ≤ C / (R - r) := h_grad x
    have h1 : ‖fderiv ℝ η x‖^2 ≤ (C / (R - r))^2 := by
      apply sq_le_sq'
      · calc -(C / (R - r)) ≤ 0 := by
              apply neg_nonpos_of_nonneg
              exact div_nonneg hC (sub_pos.mpr hRr).le
          _ ≤ ‖fderiv ℝ η x‖ := h_nonneg
      · exact h_bound
    calc (u x)^2 * ‖fderiv ℝ η x‖^2
        ≤ (u x)^2 * (C / (R - r))^2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = (C / (R - r))^2 * (u x)^2 := mul_comm _ _
  -- Step 2: Integrate both sides
  have h_mono := setIntegral_mono h_integ' (h_integ.const_mul _) h_pointwise
  -- Step 3: Pull constant out of integral on RHS
  have h_const : ∫ x in closedBall (0 : Fin 3 → ℝ) R, (C / (R - r))^2 * (u x)^2 =
                 (C / (R - r))^2 * ∫ x in closedBall (0 : Fin 3 → ℝ) R, (u x)^2 := by
    simp only [← smul_eq_mul]
    exact integral_smul ((C / (R - r))^2) (fun x => (u x)^2)
  linarith

/--
Product rule for fderiv: ∇(η² u) = 2η(∇η)u + η²(∇u).

This is pure calculus - the chain rule and product rule applied.
The key insight is that ∇(η²) = 2η∇η by chain rule.
-/
lemma expand_gradient_eta_sq_u
    (η u : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ)
    (hη : DifferentiableAt ℝ η x)
    (hu : DifferentiableAt ℝ u x) :
    fderiv ℝ (fun y => (η y)^2 * u y) x =
    (2 * η x * u x) • fderiv ℝ η x + (η x)^2 • fderiv ℝ u x := by
  -- First, η² is differentiable
  have hη2 : DifferentiableAt ℝ (fun y => (η y)^2) x := hη.pow 2
  -- Rewrite the function as a product
  have h_eq : (fun y => (η y)^2 * u y) = (fun y => (η y)^2) * u := rfl
  rw [h_eq, fderiv_mul hη2 hu]
  -- Now expand fderiv(η²) using chain rule
  have h_chain : fderiv ℝ (fun y => (η y)^2) x = (2 * η x) • fderiv ℝ η x := by
    have := fderiv_pow 2 hη
    simp only [pow_one, Nat.add_one_sub_one] at this
    rw [this]
    ring_nf
  rw [h_chain]
  -- Simplify: (2η·u)•∇η + η²•∇u
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/--
Inner product of gradients with expanded test function.

When testing with φ = η²u, the gradient inner product expands to:
  ⟨∇u, ∇(η²u)⟩ = 2ηu⟨∇u, ∇η⟩ + η²‖∇u‖²

This follows from `expand_gradient_eta_sq_u` and properties of inner product.
-/
lemma gradient_inner_product_expansion
    (η u : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ)
    (hη : DifferentiableAt ℝ η x)
    (hu : DifferentiableAt ℝ u x) :
    ∑ i : Fin 3, (fderiv ℝ u x) (Pi.single i 1) * (fderiv ℝ (fun y => (η y)^2 * u y) x) (Pi.single i 1) =
    2 * η x * u x * ∑ i : Fin 3, (fderiv ℝ u x) (Pi.single i 1) * (fderiv ℝ η x) (Pi.single i 1) +
    (η x)^2 * ∑ i : Fin 3, ((fderiv ℝ u x) (Pi.single i 1))^2 := by
  -- Use the expansion lemma
  have h_expand := expand_gradient_eta_sq_u η u x hη hu
  -- Apply the expansion pointwise in the sum
  have h_sum : ∑ i : Fin 3, (fderiv ℝ u x) (Pi.single i 1) * (fderiv ℝ (fun y => (η y)^2 * u y) x) (Pi.single i 1) =
    ∑ i : Fin 3, (fderiv ℝ u x) (Pi.single i 1) *
      (2 * η x * u x * (fderiv ℝ η x) (Pi.single i 1) + (η x)^2 * (fderiv ℝ u x) (Pi.single i 1)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [h_expand]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [h_sum]
  -- Now distribute and regroup
  simp only [mul_add, Finset.sum_add_distrib]
  -- Both sides are sums that should match after ring arithmetic
  congr 1
  · -- First term: show Σᵢ(∂u/∂xᵢ)·(2ηu·∂η/∂xᵢ) = 2ηu·Σᵢ(∂u/∂xᵢ)(∂η/∂xᵢ)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · -- Second term: show Σᵢ(∂u/∂xᵢ)·(η²·∂u/∂xᵢ) = η²·Σᵢ(∂u/∂xᵢ)²
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/--
Coordinate-wise Young inequality for gradient inner products.

For the cross term 2ηu⟨∇u,∇η⟩ = 2ηu Σᵢ(∂ᵢu)(∂ᵢη), we have:
  |2ηu Σᵢ(∂ᵢu)(∂ᵢη)| ≤ η² Σᵢ(∂ᵢu)² + u² Σᵢ(∂ᵢη)²
                      = η² · gradientSq u + u² · gradientSq η

This is the key pointwise estimate for Caccioppoli absorption.
-/
lemma coordwise_young_for_gradient
    (η_val u_val : ℝ) (du dη : Fin 3 → ℝ) :
    |2 * η_val * u_val * ∑ i : Fin 3, du i * dη i| ≤
    η_val^2 * ∑ i : Fin 3, (du i)^2 + u_val^2 * ∑ i : Fin 3, (dη i)^2 := by
  -- Step 1: Cauchy-Schwarz gives (∑ du i * dη i)² ≤ (∑ (du i)²) * (∑ (dη i)²)
  have h_cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ du dη

  -- Step 2: Let A = ∑ (du i)² and B = ∑ (dη i)²
  set A := ∑ i : Fin 3, (du i)^2 with hA_def
  set B := ∑ i : Fin 3, (dη i)^2 with hB_def

  -- Step 3: A, B are non-negative (sums of squares)
  have hA_nn : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg (du i)
  have hB_nn : 0 ≤ B := Finset.sum_nonneg fun i _ => sq_nonneg (dη i)

  -- Step 4: From Cauchy-Schwarz: |∑ du i * dη i| ≤ √A * √B
  have h_inner_bound : |∑ i : Fin 3, du i * dη i| ≤ Real.sqrt A * Real.sqrt B := by
    have h_sq : (∑ i : Fin 3, du i * dη i)^2 ≤ A * B := by
      convert h_cs using 2 <;> simp only [Finset.sum_univ_eq_sum_Fin, sq]
    have h_prod_nn : 0 ≤ Real.sqrt A * Real.sqrt B :=
      mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)
    apply abs_le_of_sq_le_sq _ h_prod_nn
    calc (∑ i : Fin 3, du i * dη i)^2
        ≤ A * B := h_sq
      _ = Real.sqrt A ^ 2 * Real.sqrt B ^ 2 := by rw [Real.sq_sqrt hA_nn, Real.sq_sqrt hB_nn]
      _ = (Real.sqrt A * Real.sqrt B) ^ 2 := by ring

  -- Step 5: |2 * η * u * (sum)| = 2 * |η| * |u| * |sum|
  have h_abs_expand : |2 * η_val * u_val * ∑ i : Fin 3, du i * dη i| =
      2 * |η_val| * |u_val| * |∑ i : Fin 3, du i * dη i| := by
    rw [abs_mul, abs_mul, abs_mul]
    simp only [abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [h_abs_expand]

  -- Step 6: Apply the bound from Step 4
  calc 2 * |η_val| * |u_val| * |∑ i : Fin 3, du i * dη i|
      ≤ 2 * |η_val| * |u_val| * (Real.sqrt A * Real.sqrt B) := by
          apply mul_le_mul_of_nonneg_left h_inner_bound
          apply mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (abs_nonneg _)) (abs_nonneg _)
    _ = 2 * (|η_val| * Real.sqrt A) * (|u_val| * Real.sqrt B) := by ring
    _ ≤ (|η_val| * Real.sqrt A)^2 + (|u_val| * Real.sqrt B)^2 := two_mul_le_add_sq _ _
    _ = η_val^2 * A + u_val^2 * B := by
        simp only [mul_pow, sq_abs, Real.sq_sqrt hA_nn, Real.sq_sqrt hB_nn]
    _ = η_val^2 * ∑ i : Fin 3, (du i)^2 + u_val^2 * ∑ i : Fin 3, (dη i)^2 := by rw [← hA_def, ← hB_def]

/--
Scaled coordinate-wise Young inequality (ε = 1/2 version for absorption).

For the absorption argument we need:
  |2ηu⟨∇u,∇η⟩| ≤ (1/2)η²·gradientSq u + 2u²·gradientSq η

This is derived from 2xy ≤ εx² + y²/ε with ε = 1/2.
-/
lemma coordwise_young_for_gradient_half
    (η_val u_val : ℝ) (du dη : Fin 3 → ℝ) :
    |2 * η_val * u_val * ∑ i : Fin 3, du i * dη i| ≤
    (1/2) * η_val^2 * ∑ i : Fin 3, (du i)^2 + 2 * u_val^2 * ∑ i : Fin 3, (dη i)^2 := by
  -- Use the basic Cauchy-Schwarz structure but with ε = 1/2
  have h_cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ du dη
  set A := ∑ i : Fin 3, (du i)^2 with hA_def
  set B := ∑ i : Fin 3, (dη i)^2 with hB_def
  have hA_nn : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg (du i)
  have hB_nn : 0 ≤ B := Finset.sum_nonneg fun i _ => sq_nonneg (dη i)

  -- Cauchy-Schwarz: |∑ du i * dη i| ≤ √A * √B
  have h_inner_bound : |∑ i : Fin 3, du i * dη i| ≤ Real.sqrt A * Real.sqrt B := by
    have h_sq : (∑ i : Fin 3, du i * dη i)^2 ≤ A * B := by
      convert h_cs using 2 <;> simp only [Finset.sum_univ_eq_sum_Fin, sq]
    have h_prod_nn : 0 ≤ Real.sqrt A * Real.sqrt B :=
      mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)
    apply abs_le_of_sq_le_sq _ h_prod_nn
    calc (∑ i : Fin 3, du i * dη i)^2
        ≤ A * B := h_sq
      _ = Real.sqrt A ^ 2 * Real.sqrt B ^ 2 := by rw [Real.sq_sqrt hA_nn, Real.sq_sqrt hB_nn]
      _ = (Real.sqrt A * Real.sqrt B) ^ 2 := by ring

  -- Expand |2 * η * u * (sum)| = 2 * |η| * |u| * |sum|
  have h_abs_expand : |2 * η_val * u_val * ∑ i : Fin 3, du i * dη i| =
      2 * |η_val| * |u_val| * |∑ i : Fin 3, du i * dη i| := by
    rw [abs_mul, abs_mul, abs_mul]
    simp only [abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [h_abs_expand]

  -- Key: Use ε = 1/2 in Young's inequality 2xy ≤ εx² + y²/ε
  -- With x = |η|√A and y = |u|√B:
  -- 2·|η|√A·|u|√B ≤ (1/2)(|η|√A)² + 2(|u|√B)² = (1/2)η²A + 2u²B
  have h_young_half : 2 * (|η_val| * Real.sqrt A) * (|u_val| * Real.sqrt B) ≤
      (1/2) * (|η_val| * Real.sqrt A)^2 + 2 * (|u_val| * Real.sqrt B)^2 := by
    have hε : (0:ℝ) < 1/2 := by norm_num
    set x := |η_val| * Real.sqrt A with hx_def
    set y := |u_val| * Real.sqrt B with hy_def
    have hx_nn : 0 ≤ x := mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
    have hy_nn : 0 ≤ y := mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
    have := young_inequality x y (1/2) hε
    calc 2 * x * y = 2 * (x * y) := by ring
      _ = 2 * |x * y| := by rw [abs_of_nonneg (mul_nonneg hx_nn hy_nn)]
      _ ≤ (1/2) * x^2 + y^2 / (1/2) := this
      _ = (1/2) * x^2 + 2 * y^2 := by ring

  calc 2 * |η_val| * |u_val| * |∑ i : Fin 3, du i * dη i|
      ≤ 2 * |η_val| * |u_val| * (Real.sqrt A * Real.sqrt B) := by
          apply mul_le_mul_of_nonneg_left h_inner_bound
          apply mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (abs_nonneg _)) (abs_nonneg _)
    _ = 2 * (|η_val| * Real.sqrt A) * (|u_val| * Real.sqrt B) := by ring
    _ ≤ (1/2) * (|η_val| * Real.sqrt A)^2 + 2 * (|u_val| * Real.sqrt B)^2 := h_young_half
    _ = (1/2) * η_val^2 * A + 2 * u_val^2 * B := by
        simp only [mul_pow, sq_abs, Real.sq_sqrt hA_nn, Real.sq_sqrt hB_nn]; ring
    _ = (1/2) * η_val^2 * ∑ i : Fin 3, (du i)^2 + 2 * u_val^2 * ∑ i : Fin 3, (dη i)^2 := by
        rw [← hA_def, ← hB_def]

/--
Caccioppoli absorption step (abstract version):
If A + 2B = 0 and A ≥ 0, then A ≤ |2B|.

This is used when:
- A = ∫ η²|∇u|² (the good gradient term)
- B = ∫ ηu⟨∇u,∇η⟩ (the cross term)
- The identity A + 2B = 0 comes from weak harmonicity
-/
lemma caccioppoli_absorption_step
    (A B : ℝ) (hAB : A + 2 * B = 0) (_hA_nonneg : 0 ≤ A) :
    A ≤ |2 * B| := by
  -- From A + 2B = 0, we have A = -2B
  have hA : A = -(2 * B) := by linarith
  rw [hA]
  -- Need: -(2*B) ≤ |2*B|
  exact neg_le_abs (2 * B)

/--
Integral cross-term bound via pointwise Young's inequality.

Pointwise: |2 * a * b| ≤ a² + b² (Young with ε=1)
Integrated: ∫ |2ab| ≤ ∫ a² + ∫ b² for integrable a², b²
-/
lemma integral_cross_term_bound
    (f g : (Fin 3 → ℝ) → ℝ) (S : Set (Fin 3 → ℝ))
    (hf_integ : IntegrableOn (fun x => (f x)^2) S)
    (hg_integ : IntegrableOn (fun x => (g x)^2) S)
    (hfg_integ : IntegrableOn (fun x => |2 * f x * g x|) S) :
    ∫ x in S, |2 * f x * g x| ≤
    (∫ x in S, (f x)^2) + ∫ x in S, (g x)^2 := by
  -- Pointwise inequality: |2ab| ≤ a² + b²
  have h_pointwise : ∀ x, |2 * f x * g x| ≤ (f x)^2 + (g x)^2 := fun x => by
    -- two_mul_le_add_sq applied to |f x| and |g x| gives:
    -- 2 * |f x| * |g x| ≤ |f x|² + |g x|²
    have h := two_mul_le_add_sq |f x| |g x|
    have h1 : |2 * f x * g x| = 2 * |f x * g x| := by
      -- 2 * f x * g x = 2 * (f x * g x) by associativity
      have h_assoc : 2 * f x * g x = 2 * (f x * g x) := by ring
      rw [h_assoc, abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2)]
    have h2 : |f x * g x| = |f x| * |g x| := abs_mul (f x) (g x)
    have h3 : |f x|^2 = (f x)^2 := sq_abs (f x)
    have h4 : |g x|^2 = (g x)^2 := sq_abs (g x)
    rw [h1, h2]
    have h_assoc : 2 * (|f x| * |g x|) = 2 * |f x| * |g x| := by ring
    rw [h_assoc]
    calc 2 * |f x| * |g x| ≤ |f x|^2 + |g x|^2 := h
      _ = (f x)^2 + (g x)^2 := by rw [h3, h4]
  -- Integrate both sides
  have h_rhs_integ : IntegrableOn (fun x => (f x)^2 + (g x)^2) S := hf_integ.add hg_integ
  have h_mono := setIntegral_mono hfg_integ h_rhs_integ h_pointwise
  -- The RHS equals the sum of integrals by integral_add
  -- Technical note: integral_add uses bound variable 'a' but goal uses 'x'
  -- These are definitionally equal but Lean 4 requires explicit conversion
  -- The proof is: h_mono gives ∫|2fg| ≤ ∫(f²+g²), and integral_add gives ∫(f²+g²) = ∫f² + ∫g²
  -- The integral equality - Lean 4 requires explicit type coercion for bound variable names
  -- Proof: h_mono gives ∫|2fg| ≤ ∫(f²+g²), integral_add gives ∫(f²+g²) = ∫f² + ∫g²
  -- The bound variable naming (x vs a) is purely syntactic - the integrals are definitionally equal
  -- However, Lean 4's definitional equality doesn't include alpha-conversion for binders
  -- So we use a direct proof that works around this limitation
  have h_split := integral_add hf_integ hg_integ
  -- h_mono : ∫ x, |2*f*g| ≤ ∫ x, (f²+g²)
  -- h_split : ∫ a, (f²+g²) = (∫ a, f²) + (∫ a, g²)
  -- Goal: ∫ x, |2*f*g| ≤ (∫ x, f²) + (∫ x, g²)
  -- The goal requires showing ∫|2fg| ≤ ∫f² + ∫g²
  -- We have h_mono: ∫|2fg| ≤ ∫(f²+g²) and h_split: ∫(f²+g²) = ∫f² + ∫g²
  -- The binder names differ (x vs a) but the integrals are semantically equal
  -- The key insight: h_split gives us ∫(f²+g²) = (∫f²) + (∫g²)
  -- The bound variable names (x vs a) are purely syntactic - integrals have the same value
  -- We prove this by transitivity through the explicit intermediate form
  have h_goal_eq : (∫ a in S, (f a)^2) + ∫ a in S, (g a)^2 =
                   (∫ x in S, (f x)^2) + ∫ x in S, (g x)^2 := rfl
  calc ∫ x in S, |2 * f x * g x|
      ≤ ∫ x in S, ((f x)^2 + (g x)^2) := h_mono
    _ = (∫ a in S, (f a)^2) + ∫ a in S, (g a)^2 := h_split
    _ = (∫ x in S, (f x)^2) + ∫ x in S, (g x)^2 := h_goal_eq

/-!
## Integration Splitting and Absorption Lemmas

These abstract lemmas handle the technical integration plumbing for Caccioppoli.
-/

/--
Split a set integral of `f + c*g` into `∫ f + c * ∫ g`.

This is used to turn the weak formulation identity `∫(A + 2B) = 0`
into the separated form `∫A + 2∫B = 0` needed for absorption.
-/
lemma set_integral_split_with_const
    {f g : (Fin 3 → ℝ) → ℝ} {c : ℝ} {S : Set (Fin 3 → ℝ)}
    (hf : IntegrableOn f S)
    (hg : IntegrableOn g S)
    (h : ∫ x in S, f x + c * g x = 0) :
    (∫ x in S, f x) + c * (∫ x in S, g x) = 0 := by
  -- Use linearity: ∫(f + c*g) = ∫f + ∫(c*g) = ∫f + c*∫g
  have h_add := integral_add hf (hg.const_mul c)
  have h_const : ∫ x in S, c * g x = c * ∫ x in S, g x := by
    simp only [← smul_eq_mul]
    exact integral_smul c (fun x => g x)
  -- Combine
  calc (∫ x in S, f x) + c * (∫ x in S, g x)
      = (∫ x in S, f x) + (∫ x in S, c * g x) := by rw [h_const]
    _ = ∫ x in S, f x + c * g x := by rw [← h_add]
    _ = 0 := h

/--
Purely algebraic absorption lemma on ℝ.

If `a ≥ 0`, `c ≥ 0`, `a + 2*b = 0` and `|2*b| ≤ (1/2)*a + 2*c`, then `a ≤ 4*c`.

This is the core algebraic step in Caccioppoli absorption, separated from integrals.
-/
lemma real_absorption {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h_eq : a + 2 * b = 0) (h_bound : |2 * b| ≤ (1/2) * a + 2 * c) :
    a ≤ 4 * c := by
  -- From a + 2b = 0: a = -2b
  have ha_eq : a = -2 * b := by linarith
  -- Since a ≥ 0 and a = -2b, we have b ≤ 0
  have hb_nonpos : b ≤ 0 := by linarith
  -- So 2b ≤ 0, thus |2b| = -2b = a
  have h_abs : |2 * b| = a := by
    have h2b_nonpos : 2 * b ≤ 0 := by linarith
    rw [abs_of_nonpos h2b_nonpos]
    linarith
  -- Substituting into bound: a ≤ (1/2)a + 2c
  have h_ineq : a ≤ (1/2) * a + 2 * c := by
    calc a = |2 * b| := h_abs.symm
      _ ≤ (1/2) * a + 2 * c := h_bound
  -- Rearranging: (1/2)a ≤ 2c, so a ≤ 4c
  nlinarith

/--
Abstract absorption lemma for Caccioppoli-type estimates.

Given:
- `(∫ A) + 2 * (∫ B) = 0` (from weak formulation)
- `|2 * B x| ≤ (1/2) * A x + 2 * C x` pointwise (from scaled Young)
- A, C ≥ 0 and all functions integrable

Conclude: `∫ A ≤ 4 * ∫ C`

The key insight: A + 2B = 0 means A = -2B, so A = |2B| (since A ≥ 0 implies B ≤ 0).
Then |2B| ≤ (1/2)A + 2C gives A ≤ (1/2)A + 2C, so (1/2)A ≤ 2C, i.e., A ≤ 4C.
-/
lemma absorption_from_cross_bound
    {A B C : (Fin 3 → ℝ) → ℝ} {S : Set (Fin 3 → ℝ)}
    (hS_meas : MeasurableSet S)
    (hA_int : IntegrableOn A S)
    (hB_int : IntegrableOn B S)
    (hC_int : IntegrableOn C S)
    (hA_nonneg : ∀ x ∈ S, 0 ≤ A x)
    (hC_nonneg : ∀ x ∈ S, 0 ≤ C x)
    (h_identity : (∫ x in S, A x) + 2 * (∫ x in S, B x) = 0)
    (h_pt : ∀ x ∈ S, |2 * B x| ≤ (1/2) * A x + 2 * C x) :
    ∫ x in S, A x ≤ 4 * ∫ x in S, C x := by
  -- Abbreviations for the integrals
  set intA := ∫ x in S, A x
  set intB := ∫ x in S, B x
  set intC := ∫ x in S, C x

  -- Step 1: ∫A ≥ 0 and ∫C ≥ 0 since A, C ≥ 0 pointwise
  have h_intA_nonneg : 0 ≤ intA := setIntegral_nonneg hS_meas (fun x hx => hA_nonneg x hx)
  have h_intC_nonneg : 0 ≤ intC := setIntegral_nonneg hS_meas (fun x hx => hC_nonneg x hx)

  -- Step 2: Get integrated bound |2∫B| ≤ (1/2)∫A + 2∫C
  -- First, ∫|2B| ≤ ∫((1/2)A + 2C) by integral monotonicity
  have h_bound_int : IntegrableOn (fun x => (1/2) * A x + 2 * C x) S :=
    (hA_int.const_mul (1/2)).add (hC_int.const_mul 2)
  have h_abs_B_int : IntegrableOn (fun x => |2 * B x|) S :=
    (hB_int.const_mul 2).abs

  -- Use pointwise bound directly with setIntegral_mono_on
  have h_int_mono : ∫ x in S, |2 * B x| ≤ ∫ x in S, (1/2) * A x + 2 * C x :=
    setIntegral_mono_on h_abs_B_int h_bound_int hS_meas (fun x hx => h_pt x hx)

  -- Split RHS integral using linearity
  have h_split : ∫ x in S, (1/2) * A x + 2 * C x = (1/2) * intA + 2 * intC := by
    have h1 : ∫ x in S, (1/2 : ℝ) * A x = (1/2) * intA := by
      simp only [← smul_eq_mul]; exact integral_smul (1/2) A
    have h2 : ∫ x in S, (2 : ℝ) * C x = 2 * intC := by
      simp only [← smul_eq_mul]; exact integral_smul 2 C
    calc ∫ x in S, (1/2) * A x + 2 * C x
        = (∫ x in S, (1/2) * A x) + ∫ x in S, (2 : ℝ) * C x :=
            integral_add (hA_int.const_mul (1/2)) (hC_int.const_mul 2)
      _ = (1/2) * intA + 2 * intC := by rw [h1, h2]

  -- So ∫|2B| ≤ (1/2)∫A + 2∫C
  have h_int_bound : ∫ x in S, |2 * B x| ≤ (1/2) * intA + 2 * intC := by
    calc ∫ x in S, |2 * B x|
        ≤ ∫ x in S, (1/2) * A x + 2 * C x := h_int_mono
      _ = (1/2) * intA + 2 * intC := h_split

  -- Use |∫(2B)| ≤ ∫|2B| and ∫(2B) = 2∫B
  have h2B_int : IntegrableOn (fun x => 2 * B x) S := hB_int.const_mul 2
  have h_abs_int : |∫ x in S, 2 * B x| ≤ ∫ x in S, |2 * B x| :=
    abs_integral_le_integral_abs (f := fun x => 2 * B x) (μ := volume.restrict S)
  have h_2B_eq : ∫ x in S, 2 * B x = 2 * intB := by
    simp only [← smul_eq_mul]; exact integral_smul 2 B

  -- So |2∫B| ≤ (1/2)∫A + 2∫C
  have h_scalar_bound : |2 * intB| ≤ (1/2) * intA + 2 * intC := by
    calc |2 * intB|
        = |∫ x in S, 2 * B x| := by rw [← h_2B_eq]
      _ ≤ ∫ x in S, |2 * B x| := h_abs_int
      _ ≤ (1/2) * intA + 2 * intC := h_int_bound

  -- Apply the algebraic absorption lemma
  exact real_absorption h_intA_nonneg h_intC_nonneg h_identity h_scalar_bound

/--
Main theorem: Elliptic Caccioppoli inequality.

Given harmonic u on B_R, energy on smaller ball B_r is controlled
by L² norm on B_R, with factor 1/(R-r)² from the cutoff.

The hypothesis `hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u` ensures that the test
function φ = η²u satisfies the smoothness requirement in the weak formulation.

Note: We use `(⊤ : ℕ∞)` to match the cutoff function's smoothness type.
This means C^∞ smooth (not analytic).
-/
theorem caccioppoli_elliptic
    (hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (h_harmonic : IsHarmonicOn u R)
    (hr : 0 < r) (hR : r < R)
    (h_u_integ : IntegrableOn (fun x => (u x)^2) (closedBall (0 : Fin 3 → ℝ) R))
    (h_grad_integ : IntegrableOn (fun x => ‖fderiv ℝ u x‖^2) (closedBall (0 : Fin 3 → ℝ) R)) :
    ∃ C > 0,
      ∫ x in closedBall (0 : Fin 3 → ℝ) r, ‖fderiv ℝ u x‖^2 ≤
        C / (R - r)^2 * ∫ x in closedBall (0 : Fin 3 → ℝ) R, (u x)^2 := by

  /-
  ## Step 1: Obtain cutoff function η
  Use HPDE_common.exists_smooth_cutoff_ball to get η with:
  - η smooth (C^∞)
  - η = 1 on B_r
  - η = 0 outside B_R
  - 0 ≤ η ≤ 1
  - ‖∇η‖ ≤ C₀/(R-r) for some universal C₀
  -/
  obtain ⟨η, h_smooth, h_one, h_zero, h_bounds, C₀, hC₀, h_grad⟩ :=
    HPDE_common.exists_smooth_cutoff_ball r R hr hR

  /-
  ## Step 2: Define test function φ = η²u
  Since Δu = 0 weakly, integration by parts gives: ∫ ∇u · ∇(η²u) = 0
  -/

  /-
  ## Step 3: Expand ∇(η²u) using product rule
  ∇(η²u) = 2η(∇η)u + η²∇u
  So the weak formulation gives:
    ∫ ∇u · (2η(∇η)u + η²∇u) = 0
    ∫ η²|∇u|² + 2∫ ηu ⟨∇u, ∇η⟩ = 0
  -/

  /-
  ## Step 4: Rearrange to isolate gradient term
    ∫ η²|∇u|² = -2∫ ηu ⟨∇u, ∇η⟩
  -/

  /-
  ## Step 5: Estimate cross term with Cauchy-Schwarz + Young's inequality
  Using 2|ab| ≤ εa² + b²/ε:
    |2∫ ηu ⟨∇u, ∇η⟩| ≤ 2∫ |η||u||∇u||∇η|
                     ≤ ∫ η²|∇u|² + ∫ u²|∇η|²  (choosing ε = 1)

  This gives:
    ∫ η²|∇u|² ≤ ∫ u²|∇η|²
  -/

  /-
  ## Step 6: Apply gradient bound and conclude
  Using ‖∇η‖ ≤ C₀/(R-r):
    ∫ u²|∇η|² ≤ (C₀/(R-r))² ∫ u²

  Since η = 1 on B_r:
    ∫_{B_r} |∇u|² ≤ ∫ η²|∇u|² ≤ (C₀/(R-r))² ∫_{B_R} u²

  So C = C₀² works.
  -/

  -- The constant is 4C₀² (the factor 4 comes from the absorption argument)
  use 4 * C₀^2
  constructor
  · -- 4C₀² > 0 since C₀ > 0
    exact mul_pos (by norm_num : (0:ℝ) < 4) (sq_pos_of_pos hC₀)

  /-
  ## Proof Structure (with sub-lemmas)

  The proof proceeds in several steps, each using our helper lemmas:

  **Step A: Test function validity**
  φ = η²u is a valid test function because:
  - η is C^∞ (from cutoff lemma)
  - u is implicitly smooth in weak formulation domain
  - Products of smooth functions are smooth
  - η = 0 outside B_R implies φ = 0 outside B_R

  **Step B: Weak formulation gives integral identity**
  From `h_harmonic` with φ = η²u:
    ∫_{B_R} Σᵢ (∂u/∂xᵢ)(∂(η²u)/∂xᵢ) = 0

  **Step C: Gradient expansion (using `gradient_inner_product_expansion`)**
  For each x:
    Σᵢ (∂u/∂xᵢ)(∂(η²u)/∂xᵢ) = 2ηu·Σᵢ(∂u/∂xᵢ)(∂η/∂xᵢ) + η²·Σᵢ(∂u/∂xᵢ)²

  Integrating and using linearity:
    ∫ η²|∇u|² + 2∫ ηu⟨∇u,∇η⟩ = 0

  **Step D: Cross-term bound (integral Young's inequality)**
  Pointwise: |2ηu⟨∇u,∇η⟩| ≤ η²|∇u|² + u²|∇η|² (Young with ε=1)
  Therefore: |2∫ ηu⟨∇u,∇η⟩| ≤ ∫(η²|∇u|² + u²|∇η|²)

  Combined with Step C (where ∫ η²|∇u|² = -2∫ ηu⟨∇u,∇η⟩):
    ∫ η²|∇u|² ≤ ∫ u²|∇η|²

  **Step E: Inner ball restriction (using `inner_ball_energy_bound`)**
  Since η = 1 on B_r:
    ∫_{B_r} |∇u|² ≤ ∫_{B_R} η²|∇u|²

  **Step F: Gradient bound (using `gradient_bound_estimate`)**
  Since ‖∇η‖ ≤ C₀/(R-r):
    ∫_{B_R} u²|∇η|² ≤ (C₀/(R-r))² ∫_{B_R} u²

  **Step G: Combine**
    ∫_{B_r} |∇u|² ≤ ∫_{B_R} η²|∇u|²    (Step E)
                   ≤ ∫_{B_R} u²|∇η|²    (Step D)
                   ≤ C₀²/(R-r)² ∫_{B_R} u²  (Step F)

  -/

  -- ══════════════════════════════════════════════════════════════════
  -- FORMAL PROOF USING HELPER LEMMAS
  -- ══════════════════════════════════════════════════════════════════

  -- Step A: φ = η²u is a valid test function
  let φ := fun y => (η y)^2 * u y

  -- h_smooth has type ContDiff ℝ (⊤ : ℕ∞) η, which means C^∞
  -- We need the same for φ = η² * u
  have hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ := by
    -- η is C^∞, so η² is C^∞
    have h_eta_sq : ContDiff ℝ (⊤ : ℕ∞) (fun y => (η y)^2) := h_smooth.pow 2
    -- u is C^∞ (from hypothesis)
    -- Product of C^∞ functions is C^∞
    exact h_eta_sq.mul hu_smooth

  have hφ_support : ∀ x, x ∉ ball (0 : Fin 3 → ℝ) R → φ x = 0 := by
    intro x hx
    -- η = 0 outside B_R, so η² * u = 0
    have h_η_zero : η x = 0 := by
      apply h_zero x
      -- x ∉ ball 0 R means x ∈ (ball 0 R)ᶜ
      exact hx
    show (η x)^2 * u x = 0
    rw [h_η_zero, sq, zero_mul, zero_mul]

  -- Step B: Apply weak harmonicity with test function φ
  have h_weak : ∫ x in closedBall (0 : Fin 3 → ℝ) R,
      ∑ i : Fin 3, (fderiv ℝ u x) (Pi.single i 1) * (fderiv ℝ φ x) (Pi.single i 1) = 0 := by
    apply h_harmonic φ hφ_smooth hφ_support

  -- The rest requires connecting the integral identity to our helper lemmas.
  -- The mathematical structure is:
  --
  -- From h_weak and gradient_inner_product_expansion:
  --   ∫ (η²|∇u|² + 2ηu⟨∇u,∇η⟩) = 0
  --
  -- Rearranging:
  --   ∫ η²|∇u|² = -2∫ ηu⟨∇u,∇η⟩
  --
  -- By integral_cross_term_bound (Young's inequality integrated):
  --   |2∫ ηu|∇u||∇η|| ≤ ∫ η²|∇u|² + ∫ u²|∇η|²
  --
  -- The non-negative term ∫ η²|∇u|² on RHS can absorb the LHS term.
  -- After careful sign analysis (since ∫ η²|∇u|² = -2∫ cross_term):
  --   ∫ η²|∇u|² ≤ ∫ u²|∇η|²
  --
  -- Then by gradient_bound_estimate with ‖∇η‖ ≤ C₀/(R-r):
  --   ∫ u²|∇η|² ≤ (C₀/(R-r))² ∫ u²
  --
  -- And by inner_ball_energy_bound (since η = 1 on B_r):
  --   ∫_{B_r} |∇u|² ≤ ∫_{B_R} η²|∇u|²

  -- ══════════════════════════════════════════════════════════════════
  -- STEP E: Inner ball restriction via inner_ball_energy_bound
  -- ══════════════════════════════════════════════════════════════════
  -- Since η = 1 on B_r, we have: ∫_{B_r} |∇u|² ≤ ∫_{B_R} η²|∇u|²
  -- We apply inner_ball_energy_bound with f = ‖∇u‖

  -- First establish that η = 1 on closedBall (using h_one which is for closedBall)
  have h_one_closed : ∀ x ∈ closedBall (0 : Fin 3 → ℝ) r, η x = 1 := h_one

  -- Integrability of η²‖∇u‖² on B_R
  -- This follows from: η bounded (0 ≤ η ≤ 1) and h_grad_integ
  -- Mathematical argument: η² ≤ 1 since η ∈ [0,1], so η²·g ≤ g for g ≥ 0
  have h_eta_sq_grad_integ : IntegrableOn (fun x => (η x)^2 * ‖fderiv ℝ u x‖^2)
                            (closedBall (0 : Fin 3 → ℝ) R) := by
    -- η² ≤ 1 pointwise, so η²·‖∇u‖² ≤ ‖∇u‖² which is integrable
    have h_eta_sq_le : ∀ x, (η x)^2 ≤ 1 := fun x => by
      have ⟨h_nn, h_le⟩ := h_bounds x
      calc (η x)^2 ≤ 1^2 := sq_le_sq' (by linarith) h_le
           _ = 1 := one_pow 2
    -- Measurability: η is continuous (smooth), so η² * ‖∇u‖² is measurable
    have h_meas : AEStronglyMeasurable (fun x => (η x)^2 * ‖fderiv ℝ u x‖^2)
                    (volume.restrict (closedBall (0 : Fin 3 → ℝ) R)) := by
      apply AEStronglyMeasurable.mul
      · exact (h_smooth.continuous.aestronglyMeasurable.pow 2).restrict
      · exact h_grad_integ.aestronglyMeasurable
    -- Pointwise bound: η² * ‖∇u‖² ≤ ‖∇u‖²
    have h_bound : ∀ᵐ x ∂(volume.restrict (closedBall (0 : Fin 3 → ℝ) R)),
                   ‖(η x)^2 * ‖fderiv ℝ u x‖^2‖ ≤ ‖‖fderiv ℝ u x‖^2‖ := by
      filter_upwards with x
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      calc (η x)^2 * ‖fderiv ℝ u x‖^2
          ≤ 1 * ‖fderiv ℝ u x‖^2 := mul_le_mul_of_nonneg_right (h_eta_sq_le x) (sq_nonneg _)
        _ = ‖fderiv ℝ u x‖^2 := one_mul _
    exact Integrable.mono h_grad_integ h_meas h_bound

  -- Apply inner_ball_energy_bound
  have h_inner := inner_ball_energy_bound η (fun x => ‖fderiv ℝ u x‖) r R
                    (le_of_lt hR) h_one_closed h_eta_sq_grad_integ

  -- ══════════════════════════════════════════════════════════════════
  -- STEP F: Gradient bound via gradient_bound_estimate
  -- ══════════════════════════════════════════════════════════════════
  -- Since ‖∇η‖ ≤ C₀/(R-r), we have: ∫ u²|∇η|² ≤ (C₀/(R-r))² ∫ u²

  -- Integrability of u²‖∇η‖² on B_R
  -- Mathematical argument: ‖∇η‖² ≤ (C₀/(R-r))², so u²‖∇η‖² ≤ (C₀/(R-r))² u²
  have h_u_sq_gradeta_integ : IntegrableOn (fun x => (u x)^2 * ‖fderiv ℝ η x‖^2)
                              (closedBall (0 : Fin 3 → ℝ) R) := by
    -- ‖∇η‖² ≤ (C₀/(R-r))² pointwise, so u²·‖∇η‖² ≤ (C₀/(R-r))² u²
    have h_gradeta_sq_le : ∀ x, ‖fderiv ℝ η x‖^2 ≤ (C₀ / (R - r))^2 := fun x => by
      have h := h_grad x
      have h_nn : 0 ≤ ‖fderiv ℝ η x‖ := norm_nonneg _
      have h_div_nn : 0 ≤ C₀ / (R - r) := div_nonneg (le_of_lt hC₀) (le_of_lt (sub_pos.mpr hR))
      exact sq_le_sq' (by linarith) h
    -- Measurability: u² * ‖∇η‖² is measurable
    have h_cont_fderiv : Continuous (fderiv ℝ η) :=
      h_smooth.continuous_fderiv (by decide : (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))
    have h_meas : AEStronglyMeasurable (fun x => (u x)^2 * ‖fderiv ℝ η x‖^2)
                    (volume.restrict (closedBall (0 : Fin 3 → ℝ) R)) := by
      apply AEStronglyMeasurable.mul
      · exact h_u_integ.aestronglyMeasurable
      · exact ((continuous_norm.comp h_cont_fderiv).pow 2).aestronglyMeasurable.restrict
    -- Pointwise bound: u² * ‖∇η‖² ≤ (C₀/(R-r))² * u²
    have h_bound : ∀ᵐ x ∂(volume.restrict (closedBall (0 : Fin 3 → ℝ) R)),
                   ‖(u x)^2 * ‖fderiv ℝ η x‖^2‖ ≤ ‖(C₀ / (R - r))^2 * (u x)^2‖ := by
      filter_upwards with x
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      calc (u x)^2 * ‖fderiv ℝ η x‖^2
          ≤ (u x)^2 * (C₀ / (R - r))^2 := mul_le_mul_of_nonneg_left (h_gradeta_sq_le x) (sq_nonneg _)
        _ = (C₀ / (R - r))^2 * (u x)^2 := mul_comm _ _
    exact Integrable.mono (h_u_integ.const_mul ((C₀ / (R - r))^2)) h_meas h_bound

  -- Apply gradient_bound_estimate
  have h_grad_est := gradient_bound_estimate η u C₀ R r
                      (le_of_lt hC₀) hR h_grad h_u_integ h_u_sq_gradeta_integ

  -- ══════════════════════════════════════════════════════════════════
  -- STEP D: Absorption argument (requires weak harmonicity analysis)
  -- ══════════════════════════════════════════════════════════════════
  --
  -- MATHEMATICAL PROOF (fully rigorous):
  -- ────────────────────────────────────
  -- From h_weak with φ = η²u, after applying gradient_inner_product_expansion:
  --   ∫ η²|∇u|² + 2∫ ηu⟨∇u,∇η⟩ = 0
  --
  -- Let A = ∫ η²|∇u|² ≥ 0 and B = ∫ ηu⟨∇u,∇η⟩
  -- The identity gives: A = -2B, so B ≤ 0 (since A ≥ 0)
  -- Therefore: A = |2B| = 2|B|
  --
  -- Young's inequality with ε = 1/2 gives pointwise:
  --   |2ηu⟨∇u,∇η⟩| ≤ |2η||u||∇u||∇η|
  --                ≤ (1/2)η²|∇u|² + 2u²|∇η|²
  --
  -- Integrating: 2|B| ≤ (1/2)A + 2C where C = ∫ u²|∇η|²
  -- Since A = 2|B|: A ≤ (1/2)A + 2C
  -- Rearranging: (1/2)A ≤ 2C, so A ≤ 4C ✓
  --
  -- FORMAL GAP: Need to connect:
  --   ∑ᵢ ((fderiv ℝ u x)(eᵢ))² = ‖fderiv ℝ u x‖²
  -- This is true for scalar functions on Fin n → ℝ but requires
  -- a lemma about inner product spaces / orthonormal bases.
  -- ────────────────────────────────────
  have h_absorption : ∫ x in closedBall (0 : Fin 3 → ℝ) R, (η x)^2 * ‖fderiv ℝ u x‖^2 ≤
                      4 * ∫ x in closedBall (0 : Fin 3 → ℝ) R, (u x)^2 * ‖fderiv ℝ η x‖^2 := by
    -- The proof requires:
    -- 1. gradient_inner_product_expansion to expand h_weak
    -- 2. A lemma: ∑ᵢ ((fderiv ℝ f x)(Pi.single i 1))² = ‖fderiv ℝ f x‖² for scalar f
    -- 3. Integral linearity + absorption algebra (proven in comments above)
    sorry

  -- ══════════════════════════════════════════════════════════════════
  -- FINAL CHAIN: Combine Steps E, D, F
  -- ══════════════════════════════════════════════════════════════════
  calc ∫ x in closedBall (0 : Fin 3 → ℝ) r, ‖fderiv ℝ u x‖^2
      ≤ ∫ x in closedBall (0 : Fin 3 → ℝ) R, (η x)^2 * ‖fderiv ℝ u x‖^2 := h_inner
    _ ≤ 4 * ∫ x in closedBall (0 : Fin 3 → ℝ) R, (u x)^2 * ‖fderiv ℝ η x‖^2 := h_absorption
    _ ≤ 4 * ((C₀ / (R - r))^2 * ∫ x in closedBall (0 : Fin 3 → ℝ) R, (u x)^2) := by
        apply mul_le_mul_of_nonneg_left h_grad_est (by norm_num : (0:ℝ) ≤ 4)
    _ = (4 * C₀^2) / (R - r)^2 * ∫ x in closedBall (0 : Fin 3 → ℝ) R, (u x)^2 := by
        have h_pos : 0 < R - r := sub_pos.mpr hR
        have h_ne : R - r ≠ 0 := h_pos.ne'
        field_simp [h_ne]

/--
Caccioppoli inequality using gradientSq (coordinate-based squared gradient).

This version uses `gradientSq f x = ∑ᵢ (∂f/∂xᵢ)²` which matches the weak formulation
`IsHarmonicOn` directly, avoiding the need for norm-conversion lemmas.

The absorption argument works naturally because both sides are expressed in
terms of coordinate sums.
-/
theorem caccioppoli_elliptic_gradSq
    (hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (h_harmonic : IsHarmonicOn u R)
    (hr : 0 < r) (hR : r < R)
    (h_u_integ : IntegrableOn (fun x => (u x)^2) (closedBall (0 : Fin 3 → ℝ) R))
    (h_gradSq_integ : IntegrableOn (fun x => gradientSq u x) (closedBall (0 : Fin 3 → ℝ) R)) :
    ∃ C > 0,
      ∫ x in closedBall (0 : Fin 3 → ℝ) r, gradientSq u x ≤
        C / (R - r)^2 * ∫ x in closedBall (0 : Fin 3 → ℝ) R, (u x)^2 := by

  -- Obtain cutoff function η
  obtain ⟨η, h_smooth, h_one, h_zero, h_bounds, C₀, hC₀, h_grad⟩ :=
    HPDE_common.exists_smooth_cutoff_ball r R hr hR

  -- The constant is 12C₀² (factor of 4 from absorption, 3 from gradientSq → fderiv conversion)
  use 12 * C₀^2
  constructor
  · exact mul_pos (by norm_num : (0:ℝ) < 12) (sq_pos_of_pos hC₀)

  /-
  ## PROOF STRUCTURE (following the absorption blueprint)

  **Step 1: Test function validity**
  φ = η²u is a valid test function (smooth, supported in B_R)

  **Step 2: Weak harmonicity gives integral identity**
  From h_harmonic with φ = η²u:
    ∫ ∑ᵢ (∂ᵢu)(∂ᵢ(η²u)) = 0

  **Step 3: Gradient expansion (via gradient_inner_product_expansion)**
  For each x:
    ∑ᵢ (∂ᵢu)(∂ᵢ(η²u)) = 2ηu·∑ᵢ(∂ᵢu)(∂ᵢη) + η²·∑ᵢ(∂ᵢu)²
                       = 2ηu·⟨∇u,∇η⟩ + η²·gradientSq u

  Integrating:
    ∫ η²·gradientSq u + 2∫ ηu·⟨∇u,∇η⟩ = 0

  Let A = ∫ η²·gradientSq u ≥ 0
  Let B = ∫ ηu·⟨∇u,∇η⟩
  Then: A + 2B = 0, so A = -2B

  **Step 4: Cross-term bound (via coordwise_young_for_gradient)**
  Pointwise: |2ηu·⟨∇u,∇η⟩| ≤ η²·gradientSq u + u²·gradientSq η
  Integrating: |2B| ≤ A + ∫ u²·gradientSq η

  From A + 2B = 0 and A ≥ 0, we get B ≤ 0, so |2B| = -2B = A
  Thus: A ≤ A + ∫ u²·gradientSq η
  This is trivial, but we need the *half* bound.

  Better: Use Young with ε = 1/2:
    |2ηu·⟨∇u,∇η⟩| ≤ (1/2)η²·gradientSq u + 2u²·gradientSq η
  Integrating: |2B| ≤ (1/2)A + 2∫ u²·gradientSq η
  Since A = |2B|: A ≤ (1/2)A + 2C where C = ∫ u²·gradientSq η
  Therefore: (1/2)A ≤ 2C, i.e., A ≤ 4C ✓

  **Step 5: Gradient bound on cutoff**
  gradientSq η ≤ 3·‖fderiv η‖² ≤ 3·(C₀/(R-r))²

  So: ∫ u²·gradientSq η ≤ 3(C₀/(R-r))² ∫ u²

  **Step 6: Inner ball restriction**
  Since η = 1 on B_r:
    ∫_{B_r} gradientSq u = ∫_{B_r} η²·gradientSq u ≤ ∫_{B_R} η²·gradientSq u = A

  **Step 7: Final chain**
    ∫_{B_r} gradientSq u ≤ A ≤ 4C ≤ 4·3(C₀/(R-r))² ∫_{B_R} u²
                              = 12C₀²/(R-r)² ∫_{B_R} u²
  -/

  -- ══════════════════════════════════════════════════════════════════
  -- STEP 1: Test function validity (φ = η²u)
  -- ══════════════════════════════════════════════════════════════════
  let φ := fun y => (η y)^2 * u y
  have hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ := (h_smooth.pow 2).mul hu_smooth
  have hφ_support : ∀ x, x ∉ ball (0 : Fin 3 → ℝ) R → φ x = 0 := fun x hx => by
    have hη0 : η x = 0 := h_zero x hx
    show (η x)^2 * u x = 0
    rw [hη0, sq, zero_mul, zero_mul]

  -- ══════════════════════════════════════════════════════════════════
  -- STEP 2: Weak harmonicity gives integral identity
  -- ══════════════════════════════════════════════════════════════════
  have h_weak : ∫ x in closedBall (0 : Fin 3 → ℝ) R,
      ∑ i : Fin 3, (fderiv ℝ u x) (Pi.single i 1) * (fderiv ℝ φ x) (Pi.single i 1) = 0 :=
    h_harmonic φ hφ_smooth hφ_support

  -- ══════════════════════════════════════════════════════════════════
  -- STEP 6: Inner ball restriction
  -- Since η = 1 on B_r, ∫_{B_r} gradientSq u ≤ ∫_{B_R} η²·gradientSq u
  -- ══════════════════════════════════════════════════════════════════
  -- gradientSq is a sum of squares, hence ≥ 0
  have h_gradSq_nn : ∀ x, 0 ≤ gradientSq u x := fun x =>
    Finset.sum_nonneg fun i _ => sq_nonneg _

  have h_eta_sq_gradSq_integ : IntegrableOn (fun x => (η x)^2 * gradientSq u x)
                               (closedBall (0 : Fin 3 → ℝ) R) := by
    -- η² ≤ 1 pointwise since η ∈ [0,1], so η²·gradientSq u ≤ gradientSq u
    have h_eta_sq_le : ∀ x, (η x)^2 ≤ 1 := fun x => by
      have ⟨h_nn, h_le⟩ := h_bounds x
      calc (η x)^2 ≤ 1^2 := sq_le_sq' (by linarith) h_le
           _ = 1 := one_pow 2
    have h_bound : ∀ᵐ x ∂(volume.restrict (closedBall (0 : Fin 3 → ℝ) R)),
                   ‖(η x)^2 * gradientSq u x‖ ≤ ‖gradientSq u x‖ := by
      filter_upwards with x
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (h_gradSq_nn x))]
      rw [Real.norm_of_nonneg (h_gradSq_nn x)]
      calc (η x)^2 * gradientSq u x
          ≤ 1 * gradientSq u x := mul_le_mul_of_nonneg_right (h_eta_sq_le x) (h_gradSq_nn x)
        _ = gradientSq u x := one_mul _
    -- Measurability: continuous * integrable function is measurable
    have h_meas : AEStronglyMeasurable (fun x => (η x)^2 * gradientSq u x)
                    (volume.restrict (closedBall (0 : Fin 3 → ℝ) R)) := by
      apply AEStronglyMeasurable.mul
      · exact (h_smooth.continuous.pow 2).aestronglyMeasurable.restrict
      · exact h_gradSq_integ.aestronglyMeasurable
    exact Integrable.mono h_gradSq_integ h_meas h_bound

  have h_inner_ball : ∫ x in closedBall (0 : Fin 3 → ℝ) r, gradientSq u x ≤
                      ∫ x in closedBall (0 : Fin 3 → ℝ) R, (η x)^2 * gradientSq u x := by
    -- Since η = 1 on B_r, gradientSq u = η²·gradientSq u on B_r
    have h_eq : ∀ x ∈ closedBall (0 : Fin 3 → ℝ) r, gradientSq u x = (η x)^2 * gradientSq u x :=
      fun x hx => by rw [h_one x hx, one_pow, one_mul]
    have h_int_eq : ∫ x in closedBall (0 : Fin 3 → ℝ) r, gradientSq u x =
                    ∫ x in closedBall (0 : Fin 3 → ℝ) r, (η x)^2 * gradientSq u x :=
      setIntegral_congr_fun measurableSet_closedBall h_eq
    rw [h_int_eq]
    apply setIntegral_mono_set h_eta_sq_gradSq_integ
    · -- η² · gradientSq u ≥ 0 a.e.
      filter_upwards with x
      exact mul_nonneg (sq_nonneg _) (h_gradSq_nn x)
    · -- B_r ⊆ B_R
      filter_upwards with x hx
      exact closedBall_subset_closedBall (le_of_lt hR) hx

  -- ══════════════════════════════════════════════════════════════════
  -- STEPS 3-5 + 7: Absorption argument and gradient bound
  -- This is the core of the proof, combining:
  -- - gradient_inner_product_expansion (step 3)
  -- - coordwise_young_for_gradient (step 4)
  -- - gradientSq_le_three_mul_fderiv_norm_sq (step 5)
  -- ══════════════════════════════════════════════════════════════════
  have h_absorption : ∫ x in closedBall (0 : Fin 3 → ℝ) R, (η x)^2 * gradientSq u x ≤
                      12 * C₀^2 / (R - r)^2 * ∫ x in closedBall (0 : Fin 3 → ℝ) R, (u x)^2 := by
    /-
    PROOF STRUCTURE:
    1. h_weak gives: ∫ ∑ᵢ (∂ᵢu)(∂ᵢ(η²u)) = 0
    2. gradient_inner_product_expansion gives pointwise:
       ∑ᵢ (∂ᵢu)(∂ᵢ(η²u)) = 2ηu·⟨∇u,∇η⟩ + η²·gradientSq u
    3. Integrating: A + 2B = 0 where
       A = ∫ η²·gradientSq u ≥ 0
       B = ∫ ηu·⟨∇u,∇η⟩
    4. coordwise_young_for_gradient gives pointwise:
       |2ηu·⟨∇u,∇η⟩| ≤ η²·gradientSq u + u²·gradientSq η
    5. Since A + 2B = 0 with A ≥ 0, we have B ≤ 0, so |2B| = A
    6. Using Young with ε = 1/2: |2ηu·⟨∇u,∇η⟩| ≤ (1/2)η²·gradientSq u + 2u²·gradientSq η
       Integrating: A ≤ (1/2)A + 2C where C = ∫ u²·gradientSq η
       Therefore: A ≤ 4C
    7. gradientSq η ≤ 3·‖fderiv η‖² ≤ 3·(C₀/(R-r))²
       So: C ≤ 3(C₀/(R-r))² ∫ u²
    8. Final: A ≤ 4·3(C₀/(R-r))² ∫ u² = 12C₀²/(R-r)² ∫ u²
    -/

    -- Define the cross-term function for convenience
    let cross_term := fun x => η x * u x *
      ∑ i : Fin 3, (fderiv ℝ u x) (Pi.single i 1) * (fderiv ℝ η x) (Pi.single i 1)

    -- STEP 3: Expand h_weak using gradient_inner_product_expansion
    -- We need differentiability of u and η at each point
    have hu_diff : ∀ x, DifferentiableAt ℝ u x := fun x =>
      hu_smooth.differentiable (by decide : (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)) |>.differentiableAt
    have hη_diff : ∀ x, DifferentiableAt ℝ η x := fun x =>
      h_smooth.differentiable (by decide : (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)) |>.differentiableAt

    -- The expanded integrand equals the weak form integrand
    have h_expand_ptwise : ∀ x, ∑ i : Fin 3, (fderiv ℝ u x) (Pi.single i 1) *
        (fderiv ℝ (fun y => (η y)^2 * u y) x) (Pi.single i 1) =
        2 * η x * u x * ∑ i : Fin 3, (fderiv ℝ u x) (Pi.single i 1) * (fderiv ℝ η x) (Pi.single i 1) +
        (η x)^2 * gradientSq u x := fun x => by
      have := gradient_inner_product_expansion η u x (hη_diff x) (hu_diff x)
      unfold gradientSq
      exact this

    -- The integrals split: ∫ (2·cross_term + η²·gradientSq u) = 0
    -- This gives: (∫ η²·gradientSq u) + 2·(∫ cross_term) = 0
    have h_integral_identity : (∫ x in closedBall (0 : Fin 3 → ℝ) R, (η x)^2 * gradientSq u x) +
        2 * (∫ x in closedBall (0 : Fin 3 → ℝ) R, cross_term x) = 0 := by
      -- Rewrite h_weak using the pointwise expansion
      have h_int_expand : ∫ x in closedBall (0 : Fin 3 → ℝ) R,
          ∑ i : Fin 3, (fderiv ℝ u x) (Pi.single i 1) * (fderiv ℝ φ x) (Pi.single i 1) =
          ∫ x in closedBall (0 : Fin 3 → ℝ) R,
            (2 * η x * u x * ∑ i : Fin 3, (fderiv ℝ u x) (Pi.single i 1) * (fderiv ℝ η x) (Pi.single i 1) +
             (η x)^2 * gradientSq u x) := by
        apply setIntegral_congr_fun measurableSet_closedBall
        intro x _
        exact h_expand_ptwise x
      -- Use the weak harmonicity to replace the LHS integral by 0
      -- h_weak : ∫_S ∑ᵢ (∂ᵢu)(∂ᵢφ) = 0
      have h0 : 0 = ∫ x in closedBall (0 : Fin 3 → ℝ) R,
            (2 * η x * u x * ∑ i : Fin 3, (fderiv ℝ u x) (Pi.single i 1) * (fderiv ℝ η x) (Pi.single i 1) +
             (η x)^2 * gradientSq u x) := by
        calc 0 = ∫ x in closedBall (0 : Fin 3 → ℝ) R,
                 ∑ i : Fin 3, (fderiv ℝ u x) (Pi.single i 1) * (fderiv ℝ φ x) (Pi.single i 1) := by
                   simpa using h_weak.symm
           _ = _ := h_int_expand

      -- Rewrite in terms of cross_term
      have h0' : 0 = ∫ x in closedBall (0 : Fin 3 → ℝ) R,
            2 * cross_term x + (η x)^2 * gradientSq u x := by
        have h_eq : ∀ x, 2 * η x * u x *
            ∑ i : Fin 3, (fderiv ℝ u x) (Pi.single i 1) * (fderiv ℝ η x) (Pi.single i 1) = 2 * cross_term x := by
          intro x; unfold cross_term; ring
        simpa [h_eq] using h0

      -- Rearrange: 2*cross + η²gradSq → η²gradSq + 2*cross
      have h0'' : ∫ x in closedBall (0 : Fin 3 → ℝ) R,
            (η x)^2 * gradientSq u x + 2 * cross_term x = 0 := by
        have h_comm : ∀ x, 2 * cross_term x + (η x)^2 * gradientSq u x =
            (η x)^2 * gradientSq u x + 2 * cross_term x := fun x => by ring
        simpa [← setIntegral_congr_fun measurableSet_closedBall (fun x _ => h_comm x)] using h0'.symm

      -- Integrability of η²·gradSq u
      have hA_int : IntegrableOn (fun x => (η x)^2 * gradientSq u x)
          (closedBall (0 : Fin 3 → ℝ) R) := h_eta_sq_gradSq_integ

      -- Integrability of cross_term (product of smooth functions on compact set)
      have hB_int : IntegrableOn cross_term (closedBall (0 : Fin 3 → ℝ) R) := by
        have hK : IsCompact (closedBall (0 : Fin 3 → ℝ) R) := isCompact_closedBall 0 R
        have h_cross_cont : Continuous cross_term := by
          unfold cross_term
          apply Continuous.mul
          · exact (h_smooth.continuous).mul hu_smooth.continuous
          · apply continuous_finset_sum; intro i _
            have h1 : Continuous (fun x => (fderiv ℝ u x) (Pi.single i 1)) :=
              (hu_smooth.continuous_fderiv (by decide : (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))).clm_apply continuous_const
            have h2 : Continuous (fun x => (fderiv ℝ η x) (Pi.single i 1)) :=
              (h_smooth.continuous_fderiv (by decide : (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))).clm_apply continuous_const
            exact h1.mul h2
        exact h_cross_cont.locallyIntegrable.integrableOn_isCompact hK

      -- Apply the splitting lemma
      exact set_integral_split_with_const hA_int hB_int h0''

    -- STEP 4 & 5: Use coordwise_young_for_gradient to bound cross term (ε=1 version)
    -- |2·cross_term| ≤ η²·gradientSq u + u²·gradientSq η
    have h_cross_bound : ∀ x, |2 * cross_term x| ≤
        (η x)^2 * gradientSq u x + (u x)^2 * gradientSq η x := fun x => by
      -- Unfold definitions
      have h := coordwise_young_for_gradient (η x) (u x)
                  (fun i => (fderiv ℝ u x) (Pi.single i 1))
                  (fun i => (fderiv ℝ η x) (Pi.single i 1))
      -- Need to massage into the right form
      unfold gradientSq
      convert h using 2 <;> ring

    -- STEP 4' & 5': Use coordwise_young_for_gradient_half to bound cross term (ε=1/2 version)
    -- This is the key for absorption: |2·cross_term| ≤ (1/2)η²·gradientSq u + 2u²·gradientSq η
    have h_cross_bound_half : ∀ x, |2 * cross_term x| ≤
        (1/2) * (η x)^2 * gradientSq u x + 2 * (u x)^2 * gradientSq η x := fun x => by
      have h := coordwise_young_for_gradient_half (η x) (u x)
                  (fun i => (fderiv ℝ u x) (Pi.single i 1))
                  (fun i => (fderiv ℝ η x) (Pi.single i 1))
      unfold gradientSq
      convert h using 2 <;> ring

    -- STEP 6: Absorption algebra
    -- From h_integral_identity: A + 2B = 0 where A = ∫ η²·gradSq u, B = ∫ cross_term
    -- Since A ≥ 0 (integral of non-negative), B ≤ 0, so A = |2B|
    -- Young (ε=1/2) gives: |2B| ≤ (1/2)A + 2C, so A ≤ (1/2)A + 2C, thus A ≤ 4C

    -- STEP 7: Bound on gradientSq η using h_grad
    -- gradientSq η ≤ 3·‖fderiv η‖² ≤ 3·(C₀/(R-r))²
    have h_gradSq_eta_bound : ∀ x, gradientSq η x ≤ 3 * (C₀ / (R - r))^2 := fun x => by
      calc gradientSq η x
          ≤ 3 * ‖fderiv ℝ η x‖^2 := gradientSq_le_three_mul_fderiv_norm_sq η x
        _ ≤ 3 * (C₀ / (R - r))^2 := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 3)
            have h := h_grad x
            have h_nn : 0 ≤ C₀ / (R - r) :=
              div_nonneg (le_of_lt hC₀) (le_of_lt (sub_pos.mpr hR))
            have h_neg : -(C₀ / (R - r)) ≤ ‖fderiv ℝ η x‖ :=
              le_trans (neg_nonpos_of_nonneg h_nn) (norm_nonneg _)
            exact sq_le_sq' h_neg h

    -- STEP 8: Combine to get final bound
    -- ∫ u²·gradientSq η ≤ 3(C₀/(R-r))² ∫ u²
    -- Then A ≤ 4·3(C₀/(R-r))² ∫ u² = 12C₀²/(R-r)² ∫ u²

    -- Let S, A_fun, B_fun, C_fun be as in the abstract absorption lemma
    let S : Set (Fin 3 → ℝ) := closedBall (0 : Fin 3 → ℝ) R
    let A_fun : (Fin 3 → ℝ) → ℝ := fun x => (η x)^2 * gradientSq u x
    let B_fun : (Fin 3 → ℝ) → ℝ := cross_term
    let C_fun : (Fin 3 → ℝ) → ℝ := fun x => (u x)^2 * gradientSq η x

    have hS_meas : MeasurableSet S := measurableSet_closedBall
    have hK : IsCompact S := isCompact_closedBall 0 R

    -- Integrability of A, B, C on S
    have hA_int : IntegrableOn A_fun S := h_eta_sq_gradSq_integ

    have hB_int : IntegrableOn B_fun S := by
      have h_cross_cont : Continuous cross_term := by
        unfold cross_term
        apply Continuous.mul
        · exact (h_smooth.continuous).mul hu_smooth.continuous
        · apply continuous_finset_sum; intro i _
          have h1 : Continuous (fun x => (fderiv ℝ u x) (Pi.single i 1)) :=
            (hu_smooth.continuous_fderiv (by decide : (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))).clm_apply continuous_const
          have h2 : Continuous (fun x => (fderiv ℝ η x) (Pi.single i 1)) :=
            (h_smooth.continuous_fderiv (by decide : (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))).clm_apply continuous_const
          exact h1.mul h2
      exact h_cross_cont.locallyIntegrable.integrableOn_isCompact hK

    have hC_int : IntegrableOn C_fun S := by
      have h_cont : Continuous C_fun := by
        apply Continuous.mul
        · exact hu_smooth.continuous.pow 2
        · unfold gradientSq
          apply continuous_finset_sum; intro i _
          have h2 : Continuous (fun x => (fderiv ℝ η x) (Pi.single i 1)) :=
            (h_smooth.continuous_fderiv (by decide : (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))).clm_apply continuous_const
          -- (∂η)² is h2.mul h2, but we need it as ^2 form
          have h_sq : Continuous (fun x => ((fderiv ℝ η x) (Pi.single i 1))^2) := by
            simp only [sq]; exact h2.mul h2
          exact h_sq
      exact h_cont.locallyIntegrable.integrableOn_isCompact hK

    -- Nonnegativity A, C ≥ 0
    have hA_nonneg : ∀ x ∈ S, 0 ≤ A_fun x := fun x _ =>
      mul_nonneg (sq_nonneg _) (h_gradSq_nn x)

    have hC_nonneg : ∀ x ∈ S, 0 ≤ C_fun x := fun x _ => by
      apply mul_nonneg (sq_nonneg _)
      exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

    -- Pointwise cross-bound: |2 B(x)| ≤ (1/2) A(x) + 2 C(x)
    have h_pt : ∀ x ∈ S, |2 * B_fun x| ≤ (1/2 : ℝ) * A_fun x + 2 * C_fun x := fun x _ => by
      have h := h_cross_bound_half x
      convert h using 2 <;> ring

    -- Apply the abstract absorption lemma: ∫ A ≤ 4 ∫ C
    have h_absorb_core : ∫ x in S, A_fun x ≤ 4 * ∫ x in S, C_fun x :=
      absorption_from_cross_bound hS_meas hA_int hB_int hC_int hA_nonneg hC_nonneg
        h_integral_identity h_pt

    -- Use the gradientSq η bound to control the C integral
    have hC_pointwise : ∀ x ∈ S, C_fun x ≤ 3 * (C₀ / (R - r))^2 * (u x)^2 := fun x _ => by
      have h_grad := h_gradSq_eta_bound x
      calc C_fun x = (u x)^2 * gradientSq η x := rfl
        _ ≤ (u x)^2 * (3 * (C₀ / (R - r))^2) :=
            mul_le_mul_of_nonneg_left h_grad (sq_nonneg _)
        _ = 3 * (C₀ / (R - r))^2 * (u x)^2 := by ring

    -- Monotonicity of set integrals with pointwise ≤
    have h_rhs_int : IntegrableOn (fun x => 3 * (C₀ / (R - r))^2 * (u x)^2) S :=
      (h_u_integ.const_mul (3 * (C₀ / (R - r))^2))
    have hC_mono : ∫ x in S, C_fun x ≤ ∫ x in S, 3 * (C₀ / (R - r))^2 * (u x)^2 :=
      setIntegral_mono_on hC_int h_rhs_int hS_meas hC_pointwise

    -- Pull the constant 3(C₀/(R-r))² outside the integral
    have hC_const : ∫ x in S, 3 * (C₀ / (R - r))^2 * (u x)^2 =
        3 * (C₀ / (R - r))^2 * ∫ x in S, (u x)^2 := by
      simp only [← smul_eq_mul]
      exact integral_smul (3 * (C₀ / (R - r))^2) (fun x => (u x)^2)

    -- Combine the bounds for C
    have hC_final : ∫ x in S, C_fun x ≤ 3 * (C₀ / (R - r))^2 * ∫ x in S, (u x)^2 := by
      calc ∫ x in S, C_fun x
          ≤ ∫ x in S, 3 * (C₀ / (R - r))^2 * (u x)^2 := hC_mono
        _ = 3 * (C₀ / (R - r))^2 * ∫ x in S, (u x)^2 := hC_const

    -- Final: ∫ A ≤ 4 * ∫ C ≤ 4 * 3 (C₀/(R-r))² ∫ u² = 12 C₀² / (R - r)² ∫ u²
    have h_pos : (R - r) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hR)
    calc ∫ x in S, A_fun x
        ≤ 4 * ∫ x in S, C_fun x := h_absorb_core
      _ ≤ 4 * (3 * (C₀ / (R - r))^2 * ∫ x in S, (u x)^2) := by
          apply mul_le_mul_of_nonneg_left hC_final (by norm_num : (0:ℝ) ≤ 4)
      _ = 12 * C₀^2 / (R - r)^2 * ∫ x in S, (u x)^2 := by field_simp; ring

  -- ══════════════════════════════════════════════════════════════════
  -- FINAL CHAIN: Combine inner ball restriction with absorption
  -- ══════════════════════════════════════════════════════════════════
  calc ∫ x in closedBall (0 : Fin 3 → ℝ) r, gradientSq u x
      ≤ ∫ x in closedBall (0 : Fin 3 → ℝ) R, (η x)^2 * gradientSq u x := h_inner_ball
    _ ≤ 12 * C₀^2 / (R - r)^2 * ∫ x in closedBall (0 : Fin 3 → ℝ) R, (u x)^2 := h_absorption

end HPDE_01
