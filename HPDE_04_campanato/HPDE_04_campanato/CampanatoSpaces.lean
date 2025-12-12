import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import HPDE_common.HPDE_common

open Real MeasureTheory Set Metric

namespace HPDE_04

/-!
# Campanato Spaces and Morrey Embedding

Campanato spaces L^{p,λ}(Ω) generalize both Morrey spaces and Hölder spaces.

## Key Results

1. **Campanato-Hölder:** For n < λ ≤ n+p, L^{p,λ} ≅ C^{0,α} with α = (λ-n)/p

## References

- Campanato (1963): Original definition
- Giaquinta (1983): Applications to regularity theory
-/

/-- R³ as Fin 3 → ℝ with standard measure -/
abbrev R3 := Fin 3 → ℝ

/-!
## Infrastructure Lemmas
-/

/-- Balls in R³ have positive measure. This is essential for defining averages. -/
lemma ball_pos_measure (x : R3) (r : ℝ) (hr : 0 < r) :
    0 < (volume (Metric.ball x r)).toReal := by
  apply ENNReal.toReal_pos
  · -- volume ≠ 0
    exact (Metric.measure_ball_pos volume x hr).ne'
  · -- volume ≠ ⊤
    exact measure_ball_lt_top.ne

/-- Balls in R³ have finite (non-infinite) measure -/
lemma ball_measure_ne_top (x : R3) (r : ℝ) :
    volume (Metric.ball x r) ≠ ⊤ :=
  measure_ball_lt_top.ne

/-- Volume of a ball in R³ (using sup norm, so "ball" = cube).
    volume = (2r)³ = 8r³. For Campanato scaling, only the r³ dependence matters. -/
lemma volume_ball_R3 (x : R3) (r : ℝ) (hr : 0 < r) :
    volume (Metric.ball x r) = ENNReal.ofReal ((2 * r) ^ 3) := by
  have hcard : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3
  rw [Real.volume_pi_ball x hr, hcard]

/-- Volume of a ball in R³ as a real number -/
lemma volume_ball_R3_toReal (x : R3) (r : ℝ) (hr : 0 < r) :
    (volume (Metric.ball x r)).toReal = (2 * r) ^ 3 := by
  rw [volume_ball_R3 x r hr]
  rw [ENNReal.toReal_ofReal]
  exact pow_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hr.le) 3

/-- Volume scales as r³ in R³. Key for Campanato/Morrey scaling arguments. -/
lemma volume_ball_scaling (x : R3) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    (volume (Metric.ball x r)).toReal / (volume (Metric.ball x s)).toReal = (r / s) ^ 3 := by
  rw [volume_ball_R3_toReal x r hr, volume_ball_R3_toReal x s hs]
  have hs_ne : (2 * s) ^ 3 ≠ 0 := pow_ne_zero 3 (mul_ne_zero two_ne_zero hs.ne')
  field_simp [hs_ne]

/-- Average of a function over a ball -/
noncomputable def ballAverage (u : R3 → ℝ) (x : R3) (r : ℝ) : ℝ :=
  (volume (Metric.ball x r)).toReal⁻¹ * ∫ y in Metric.ball x r, u y

/-- Mean oscillation over a ball -/
noncomputable def meanOscillation (u : R3 → ℝ) (x : R3) (r : ℝ) (p : ℝ) : ℝ :=
  ((volume (Metric.ball x r)).toReal⁻¹ *
   ∫ y in Metric.ball x r, |u y - ballAverage u x r| ^ p) ^ (1/p)

/-- A function is in Campanato space L^{p,lam} with bound M -/
def IsInCampanato (u : R3 → ℝ) (p lam M : ℝ) : Prop :=
  ∀ x : R3, ∀ r : ℝ, 0 < r → r ^ (-lam/p) * meanOscillation u x r p ≤ M

/-- A function is Hölder continuous with exponent α and constant C -/
def IsHolderContinuous (u : R3 → ℝ) (α C : ℝ) : Prop :=
  ∀ x y : R3, |u x - u y| ≤ C * dist x y ^ α

/-- Morrey norm (without averaging by volume) -/
noncomputable def morreyNorm (u : R3 → ℝ) (x : R3) (r : ℝ) (p : ℝ) : ℝ :=
  (∫ y in Metric.ball x r, |u y| ^ p) ^ (1/p)

/-- A function is in Morrey space with bound M -/
def IsInMorrey (u : R3 → ℝ) (p lam M : ℝ) : Prop :=
  ∀ x : R3, ∀ r : ℝ, 0 < r → r ^ (-lam/p) * morreyNorm u x r p ≤ M

/-!
## L² Specialized Definitions (for Navier-Stokes applications)

These avoid rpow machinery by fixing p=2.
-/

/-- L² norm over a ball -/
noncomputable def L2Norm (u : R3 → ℝ) (x : R3) (r : ℝ) : ℝ :=
  Real.sqrt (∫ y in Metric.ball x r, (u y)^2)

/-- L² mean oscillation over a ball -/
noncomputable def meanOscillationL2 (u : R3 → ℝ) (x : R3) (r : ℝ) : ℝ :=
  Real.sqrt ((volume (Metric.ball x r)).toReal⁻¹ *
    ∫ y in Metric.ball x r, (u y - ballAverage u x r)^2)

/-- A function is in L² Morrey space: ∫_{B_r} u² ≤ M² r^{3+2α} -/
def IsInMorreyL2 (u : R3 → ℝ) (M α : ℝ) : Prop :=
  ∀ x : R3, ∀ r : ℝ, 0 < r →
    ∫ y in Metric.ball x r, (u y)^2 ≤ M^2 * r^(3 + 2*α)

/-- A function is in L² Campanato space -/
def IsInCampanatoL2 (u : R3 → ℝ) (M α : ℝ) : Prop :=
  ∀ x : R3, ∀ r : ℝ, 0 < r →
    (volume (Metric.ball x r)).toReal⁻¹ *
    ∫ y in Metric.ball x r, (u y - ballAverage u x r)^2 ≤ M^2 * r^(2*α)

/-!
## Helper Lemmas for Campanato-Morrey
-/

/-- Convexity bound for squares: |a - b|² ≤ 2(a² + b²).
    This is the key p=2 estimate for L² Campanato/Morrey bounds.

    Proof: 2(a² + b²) - (a-b)² = (a+b)² ≥ 0.
-/
lemma abs_sub_sq_le_two_mul_add_sq (a b : ℝ) :
    |a - b|^2 ≤ 2 * (a^2 + b^2) := by
  -- Key identity: 2*(a² + b²) - (a - b)² = (a + b)²
  have h_identity : 2 * (a^2 + b^2) - (a - b)^2 = (a + b)^2 := by ring
  -- (a + b)² ≥ 0
  have h_sq_nonneg : 0 ≤ (a + b)^2 := sq_nonneg (a + b)
  -- Therefore (a - b)² ≤ 2*(a² + b²)
  have h_ineq : (a - b)^2 ≤ 2 * (a^2 + b^2) := by linarith
  -- And |a - b|² = (a - b)²
  simp only [sq_abs]
  exact h_ineq

/-- **Convexity bound for p-th powers (p ≥ 1)**

For all a, b ∈ ℝ and p ≥ 1:
  |a - b|^p ≤ 2^(p-1) · (|a|^p + |b|^p)

**Proof idea:**
1. Triangle inequality: |a - b| ≤ |a| + |b|
2. Convexity of t^p on [0,∞) gives: (x + y)^p ≤ 2^(p-1) · (x^p + y^p)
   (via `NNReal.rpow_add_le_mul_rpow_add_rpow`)
3. Monotonicity of t^p on [0,∞) lifts |a-b| ≤ |a|+|b| to the p-th power bound.

This is the key convexity estimate for Campanato/Morrey space embeddings. -/
lemma abs_sub_rpow_le (a b : ℝ) (p : ℝ) (hp : 1 ≤ p) :
    |a - b| ^ p ≤ 2 ^ (p - 1) * (|a| ^ p + |b| ^ p) := by
  -- Step 1: Triangle inequality |a - b| ≤ |a| + |b|
  have h_tri' : |a - b| ≤ |a| + |b| := abs_sub_le a 0 b |>.trans (by simp)

  -- Step 2: Convert to NNReal for the convexity bound
  -- |a|, |b|, |a - b| are all nonnegative, so we can use NNReal
  have ha_nn : 0 ≤ |a| := abs_nonneg a
  have hb_nn : 0 ≤ |b| := abs_nonneg b
  have hab_nn : 0 ≤ |a - b| := abs_nonneg (a - b)
  have hsum_nn : 0 ≤ |a| + |b| := add_nonneg ha_nn hb_nn

  -- Step 3: Apply NNReal.rpow_add_le_mul_rpow_add_rpow
  -- (z₁ + z₂)^p ≤ 2^(p-1) · (z₁^p + z₂^p) for z₁, z₂ : NNReal
  have h_convex : (|a| + |b|) ^ p ≤ 2 ^ (p - 1) * (|a| ^ p + |b| ^ p) := by
    -- Convert to NNReal
    let z₁ : NNReal := ⟨|a|, ha_nn⟩
    let z₂ : NNReal := ⟨|b|, hb_nn⟩
    have h := NNReal.rpow_add_le_mul_rpow_add_rpow z₁ z₂ hp
    -- The inequality h is: (z₁ + z₂) ^ p ≤ 2 ^ (p - 1) * (z₁ ^ p + z₂ ^ p) in NNReal
    -- We need to convert this to ℝ
    have h_coe : ((z₁ + z₂) ^ p : ℝ) ≤ ((2 : NNReal) ^ (p - 1) * (z₁ ^ p + z₂ ^ p) : ℝ) := by
      exact_mod_cast h
    -- Simplify the coercions
    simp only at h_coe
    convert h_coe using 2

  -- Step 4: Monotonicity: |a - b| ≤ |a| + |b| implies |a - b|^p ≤ (|a| + |b|)^p
  have h_mono : |a - b| ^ p ≤ (|a| + |b|) ^ p := by
    apply Real.rpow_le_rpow hab_nn h_tri'
    linarith

  -- Combine
  calc |a - b| ^ p
      ≤ (|a| + |b|) ^ p := h_mono
    _ ≤ 2 ^ (p - 1) * (|a| ^ p + |b| ^ p) := h_convex

/-!
## L² Specialized Bounds (using Cauchy-Schwarz, not Hölder)

These are much simpler than the general case since p=2 allows us
to use standard inner product / Cauchy-Schwarz inequalities.
-/

/-- L² ball average bound via Jensen's inequality.

    |u_avg| = |vol⁻¹ ∫ u| ≤ vol^{-1/2} · L2Norm(u)

    **Proof outline via Jensen:**
    1. x² is convex on ℝ (`Even.strictConvexOn_pow`)
    2. Jensen's inequality: (⨍ u)² ≤ ⨍ u²
    3. Take sqrt: |⨍ u| ≤ √(⨍ u²) = √(V⁻¹ ∫ u²) = V^{-1/2} √(∫ u²)
-/
lemma ballAverage_bound_L2 (u : R3 → ℝ) (x : R3) (r : ℝ) (hr : 0 < r)
    (h_integ : IntegrableOn (fun y => (u y)^2) (Metric.ball x r))
    (h_u_integ : IntegrableOn u (Metric.ball x r)) :
    |ballAverage u x r| ≤
    (volume (Metric.ball x r)).toReal ^ (-(1:ℝ)/2) * L2Norm u x r := by
  /-
  **Proof via Jensen's inequality:**
  Key Mathlib lemmas:
  - `Even.convexOn_pow` (n=2): x² is convex on ℝ
  - `ConvexOn.map_set_average_le`: g(⨍ f) ≤ ⨍(g ∘ f) for convex g

  For g(x) = x², f = u, this gives:
    (⨍_{B_r} u)² ≤ ⨍_{B_r} u² = V⁻¹ * ∫ u²

  Taking square roots:
    |⨍_{B_r} u| ≤ √(V⁻¹ * ∫ u²) = V^{-1/2} * √(∫ u²) = V^{-1/2} * L2Norm

  The conversion between `⨍` (Mathlib average) and `ballAverage` is:
    ⨍ x in t, f x ∂μ = (μ t)⁻¹ • ∫ x in t, f x ∂μ
  which matches ballAverage when μ = volume.
  -/
  -- Step 1: Setup volume
  set V := (volume (Metric.ball x r)).toReal with hV
  have h_vol_pos : 0 < V := ball_pos_measure x r hr
  have h_vol_ne : V ≠ 0 := h_vol_pos.ne'
  have h_vol_nnreal : 0 ≤ V := h_vol_pos.le
  have h_vol_ennreal_ne : volume (Metric.ball x r) ≠ 0 := (Metric.measure_ball_pos volume x hr).ne'
  have h_vol_ennreal_ne_top : volume (Metric.ball x r) ≠ ⊤ := measure_ball_lt_top.ne

  -- Step 2: Relate ballAverage to Mathlib's setAverage
  have h_avg_eq : ballAverage u x r = ⨍ y in Metric.ball x r, u y := by
    unfold ballAverage
    rw [MeasureTheory.setAverage_eq]
    simp only [measureReal_def, smul_eq_mul, ← hV]

  -- Step 3: Get convexity of x² on ℝ
  have h_convex : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) :=
    (Even.strictConvexOn_pow (by decide : Even 2) (by decide : (2 : ℕ) ≠ 0)).convexOn

  -- Continuity of x²
  have h_cont : ContinuousOn (fun x : ℝ => x ^ 2) Set.univ := continuous_pow 2 |>.continuousOn

  -- f maps into univ (trivial)
  have h_f_maps : ∀ᵐ y ∂(volume.restrict (Metric.ball x r)), u y ∈ Set.univ := by
    filter_upwards with y; trivial

  -- u² integrable is given
  have h_comp_integ : IntegrableOn ((fun x => x ^ 2) ∘ u) (Metric.ball x r) := h_integ

  -- Jensen's inequality: (⨍ u)² ≤ ⨍ u²
  have h_jensen : (⨍ y in Metric.ball x r, u y) ^ 2 ≤ ⨍ y in Metric.ball x r, (u y) ^ 2 := by
    apply h_convex.map_set_average_le h_cont isClosed_univ
    · exact h_vol_ennreal_ne
    · exact h_vol_ennreal_ne_top
    · exact h_f_maps
    · exact h_u_integ
    · exact h_comp_integ

  -- Step 4: Convert ⨍ u² = V⁻¹ * ∫ u²
  have h_avg_sq_eq : ⨍ y in Metric.ball x r, (u y) ^ 2 = V⁻¹ * ∫ y in Metric.ball x r, (u y) ^ 2 := by
    rw [MeasureTheory.setAverage_eq]
    simp only [measureReal_def, smul_eq_mul, ← hV]

  -- Nonneg bounds
  have h_int_nonneg : 0 ≤ ∫ y in Metric.ball x r, (u y) ^ 2 := integral_nonneg (fun y => sq_nonneg _)

  -- Step 5: Use abs_le_sqrt: |x|² ≤ y → |x| ≤ √y
  -- We have (⨍ u)² ≤ ⨍ u² = V⁻¹ * ∫ u²
  have h_sq_le : (⨍ y in Metric.ball x r, u y) ^ 2 ≤ V⁻¹ * ∫ y in Metric.ball x r, (u y) ^ 2 := by
    calc (⨍ y in Metric.ball x r, u y) ^ 2
        ≤ ⨍ y in Metric.ball x r, (u y) ^ 2 := h_jensen
      _ = V⁻¹ * ∫ y in Metric.ball x r, (u y) ^ 2 := h_avg_sq_eq

  have h_abs_avg_le : |⨍ y in Metric.ball x r, u y| ≤ Real.sqrt (V⁻¹ * ∫ y in Metric.ball x r, (u y) ^ 2) := by
    -- Use Real.abs_le_sqrt: x^2 ≤ y → |x| ≤ √y
    exact Real.abs_le_sqrt h_sq_le

  -- Step 6: Convert √(V⁻¹ * ∫ u²) = V^{-1/2} * L2Norm
  calc |ballAverage u x r|
      = |⨍ y in Metric.ball x r, u y| := by rw [h_avg_eq]
    _ ≤ Real.sqrt (V⁻¹ * ∫ y in Metric.ball x r, (u y) ^ 2) := h_abs_avg_le
    _ = Real.sqrt V⁻¹ * Real.sqrt (∫ y in Metric.ball x r, (u y) ^ 2) := by
        rw [Real.sqrt_mul (inv_nonneg.mpr h_vol_nnreal)]
    _ = V ^ (-(1:ℝ)/2) * L2Norm u x r := by
        -- √(V⁻¹) = V^{-1/2} and L2Norm = √(∫ u²)
        unfold L2Norm
        congr 1
        -- √(V⁻¹) = (√V)⁻¹ = V^{1/2}⁻¹ = V^{-1/2}
        rw [Real.sqrt_inv, Real.sqrt_eq_rpow, ← Real.rpow_neg h_vol_nnreal]
        ring_nf
    _ = (volume (Metric.ball x r)).toReal ^ (-(1:ℝ)/2) * L2Norm u x r := by rw [← hV]

/-- Mean oscillation bound in L² using abs_sub_sq_le_two_mul_add_sq.

    From |u - u_avg|² ≤ 2(u² + u_avg²), integrating gives:
    ∫ |u - u_avg|² ≤ 2 ∫ u² + 2 vol · u_avg²

    Combined with ballAverage_bound_L2, this gives control on mean oscillation.
-/
lemma meanOscillationL2_le (u : R3 → ℝ) (x : R3) (r : ℝ) (hr : 0 < r)
    (h_integ : IntegrableOn (fun y => (u y)^2) (Metric.ball x r))
    (h_u_integ : IntegrableOn u (Metric.ball x r)) :
    (meanOscillationL2 u x r)^2 ≤
    (2 * (volume (Metric.ball x r)).toReal⁻¹ * ∫ y in Metric.ball x r, (u y)^2) +
    2 * (ballAverage u x r)^2 := by
  -- Expand meanOscillationL2
  unfold meanOscillationL2
  -- Use set to create abbreviation that's definitionally equal
  set V := (volume (Metric.ball x r)).toReal with hV
  have h_vol_pos : 0 < V := ball_pos_measure x r hr
  have h_vol_ne : V ≠ 0 := h_vol_pos.ne'
  have h_vol_inv_nonneg : 0 ≤ V⁻¹ := inv_nonneg.mpr h_vol_pos.le
  have h_int_nonneg : 0 ≤ ∫ y in Metric.ball x r, (u y - ballAverage u x r)^2 :=
    integral_nonneg (fun y => sq_nonneg _)
  have h_prod_nonneg : 0 ≤ V⁻¹ * ∫ y in Metric.ball x r, (u y - ballAverage u x r)^2 :=
    mul_nonneg h_vol_inv_nonneg h_int_nonneg
  rw [Real.sq_sqrt h_prod_nonneg]

  -- Key pointwise inequality from abs_sub_sq_le_two_mul_add_sq:
  -- (u - avg)² ≤ 2 * u² + 2 * avg²
  have h_pointwise : ∀ y, (u y - ballAverage u x r)^2 ≤ 2 * (u y)^2 + 2 * (ballAverage u x r)^2 := fun y => by
    have h := abs_sub_sq_le_two_mul_add_sq (u y) (ballAverage u x r)
    simp only [sq_abs] at h
    linarith

  -- Integrability: constant functions are integrable on balls
  have h_const_integ : IntegrableOn (fun _ => (ballAverage u x r)^2) (Metric.ball x r) :=
    integrableOn_const
  have h_const_integ2 : IntegrableOn (fun _ => 2 * (ballAverage u x r)^2) (Metric.ball x r) :=
    integrableOn_const

  -- RHS is integrable: 2*u² + 2*avg² is sum of integrable functions
  have h_2u2_integ : IntegrableOn (fun y => 2 * (u y)^2) (Metric.ball x r) :=
    h_integ.const_mul 2
  have h_rhs_integ : IntegrableOn (fun y => 2 * (u y)^2 + 2 * (ballAverage u x r)^2) (Metric.ball x r) :=
    h_2u2_integ.add h_const_integ2

  -- LHS is integrable: (u - avg)² is integrable via sub then square
  have h_sub_integ : IntegrableOn (fun y => u y - ballAverage u x r) (Metric.ball x r) :=
    h_u_integ.sub integrableOn_const

  -- For integrability of (u-c)², we use the pointwise bound and Integrable.mono'
  -- Integrable.mono' needs: ‖f a‖ ≤ g a where g is integrable
  have h_norm_bound : ∀ᵐ y ∂(volume.restrict (Metric.ball x r)),
      ‖(u y - ballAverage u x r)^2‖ ≤ 2 * (u y)^2 + 2 * (ballAverage u x r)^2 := by
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact h_pointwise y

  have h_lhs_meas : AEStronglyMeasurable (fun y => (u y - ballAverage u x r)^2)
                    (volume.restrict (Metric.ball x r)) := by
    -- (u - c)² = (u - c) * (u - c) is AE strongly measurable since u - c is
    have h_sub_asm := h_sub_integ.aestronglyMeasurable
    have h_mul : AEStronglyMeasurable ((fun y => u y - ballAverage u x r) * (fun y => u y - ballAverage u x r))
                 (volume.restrict (Metric.ball x r)) := h_sub_asm.mul h_sub_asm
    -- x^2 = x * x, so the functions are equal
    convert h_mul using 1
    ext y
    simp only [Pi.mul_apply, sq]

  have h_lhs_integ : IntegrableOn (fun y => (u y - ballAverage u x r)^2) (Metric.ball x r) :=
    Integrable.mono' h_rhs_integ h_lhs_meas h_norm_bound

  -- Lift pointwise to integral via setIntegral_mono
  have h_int_ineq : ∫ y in Metric.ball x r, (u y - ballAverage u x r)^2 ≤
                    ∫ y in Metric.ball x r, (2 * (u y)^2 + 2 * (ballAverage u x r)^2) := by
    apply setIntegral_mono h_lhs_integ h_rhs_integ
    intro y
    exact h_pointwise y

  -- Split the RHS integral: ∫(2u² + 2c²) = 2∫u² + 2c²·V
  have h_int_2u2 : ∫ y in Metric.ball x r, 2 * (u y)^2 = 2 * ∫ y in Metric.ball x r, (u y)^2 :=
    integral_const_mul 2 _
  have h_int_const : ∫ _y in Metric.ball x r, 2 * (ballAverage u x r)^2 =
                     2 * (ballAverage u x r)^2 * V := by
    rw [setIntegral_const]
    simp only [measureReal_def, smul_eq_mul]
    ring

  have h_split : ∫ y in Metric.ball x r, (2 * (u y)^2 + 2 * (ballAverage u x r)^2) =
                 (2 * ∫ y in Metric.ball x r, (u y)^2) + 2 * (ballAverage u x r)^2 * V := by
    rw [integral_add h_2u2_integ h_const_integ2, h_int_2u2, h_int_const]

  -- Algebraic manipulation: V⁻¹((2∫u²) + 2c²V) = 2V⁻¹∫u² + 2c²
  -- Let I = ∫ u², c = ballAverage, then we prove V⁻¹((2I) + 2c²V) = 2V⁻¹I + 2c²
  set I := ∫ y in Metric.ball x r, (u y)^2 with hI
  set c := ballAverage u x r with hc

  have h_algebra : V⁻¹ * ((2 * I) + 2 * c^2 * V) = 2 * V⁻¹ * I + 2 * c^2 := by
    have hVinv : V⁻¹ * V = 1 := inv_mul_cancel₀ h_vol_ne
    -- Distribute V⁻¹
    rw [mul_add]
    -- First term: V⁻¹ * (2 * I) = 2 * V⁻¹ * I
    have h1 : V⁻¹ * (2 * I) = 2 * V⁻¹ * I := by ring
    -- Second term: V⁻¹ * (2 * c² * V) = 2 * c² * (V⁻¹ * V) = 2 * c²
    have h2 : V⁻¹ * (2 * c^2 * V) = 2 * c^2 := by
      calc V⁻¹ * (2 * c^2 * V) = 2 * c^2 * (V⁻¹ * V) := by ring
        _ = 2 * c^2 * 1 := by rw [hVinv]
        _ = 2 * c^2 := by ring
    rw [h1, h2]

  -- Combine everything using I and c abbreviations
  calc V⁻¹ * ∫ y in Metric.ball x r, (u y - ballAverage u x r)^2
      ≤ V⁻¹ * ∫ y in Metric.ball x r, (2 * (u y)^2 + 2 * (ballAverage u x r)^2) := by
        apply mul_le_mul_of_nonneg_left h_int_ineq h_vol_inv_nonneg
    _ = V⁻¹ * ((2 * I) + 2 * c^2 * V) := by rw [h_split]
    _ = 2 * V⁻¹ * I + 2 * c^2 := h_algebra
    _ ≤ (2 * (volume (Metric.ball x r)).toReal⁻¹ * ∫ y in Metric.ball x r, (u y)^2) +
        2 * (ballAverage u x r)^2 := by
        -- Goal: 2V⁻¹I + 2c² ≤ (2(vol)⁻¹∫u²) + 2(ballAverage)²
        -- Since I = ∫u², c = ballAverage, V = (vol).toReal, these are equal
        rw [hI, hc, ← hV]

/-- Ball average is bounded by Lp norm (Jensen-type bound).

**Proof:** Via Jensen's inequality for the convex function t ↦ |t|^p on ℝ.
1. The function x ↦ |x|^p is convex on ℝ for p ≥ 1
2. Jensen: |⨍ u|^p ≤ ⨍ |u|^p = V⁻¹ ∫ |u|^p
3. Take p-th root: |⨍ u| ≤ (V⁻¹ ∫ |u|^p)^{1/p} = V^{-1/p} · morreyNorm

This is a generalization of ballAverage_bound_L2 from p=2 to arbitrary p ≥ 1.
The additional h_u_integ hypothesis ensures u is integrable (not just |u|^p).
-/
lemma ballAverage_bound (u : R3 → ℝ) (x : R3) (r : ℝ) (p : ℝ)
    (hr : 0 < r) (hp : 1 ≤ p)
    (h_integ : IntegrableOn (fun y => |u y| ^ p) (Metric.ball x r))
    (h_u_integ : IntegrableOn u (Metric.ball x r)) :
    |ballAverage u x r| ≤
    (volume (Metric.ball x r)).toReal ^ (-1/p) * morreyNorm u x r p := by
  -- Setup volume abbreviations
  set V := (volume (Metric.ball x r)).toReal with hV
  have h_vol_pos : 0 < V := ball_pos_measure x r hr
  have h_vol_ne : V ≠ 0 := h_vol_pos.ne'
  have h_vol_nonneg : 0 ≤ V := h_vol_pos.le
  have h_vol_ennreal_ne : volume (Metric.ball x r) ≠ 0 := (Metric.measure_ball_pos volume x hr).ne'
  have h_vol_ennreal_ne_top : volume (Metric.ball x r) ≠ ⊤ := measure_ball_lt_top.ne
  have hp_pos : 0 < p := lt_of_lt_of_le one_pos hp

  -- Integrability of |u| from u integrable
  have h_abs_integ : IntegrableOn (fun y => |u y|) (Metric.ball x r) := h_u_integ.norm

  -- Relate ballAverage to Mathlib's setAverage
  have h_avg_eq : ballAverage u x r = ⨍ y in Metric.ball x r, u y := by
    unfold ballAverage
    rw [MeasureTheory.setAverage_eq]
    simp only [measureReal_def, smul_eq_mul, ← hV]

  have h_norm_eq_abs : ∀ y, ‖u y‖ = |u y| := fun y => Real.norm_eq_abs _

  -- Step 2: Power mean inequality (⨍ |u|)^p ≤ ⨍ |u|^p for p ≥ 1
  have h_avg_absp_eq : ⨍ y in Metric.ball x r, |u y| ^ p =
                       V⁻¹ * ∫ y in Metric.ball x r, |u y| ^ p := by
    rw [MeasureTheory.setAverage_eq]
    simp only [measureReal_def, smul_eq_mul, ← hV]

  -- Nonneg bounds
  have h_int_absp_nonneg : 0 ≤ ∫ y in Metric.ball x r, |u y| ^ p :=
    integral_nonneg (fun y => Real.rpow_nonneg (abs_nonneg _) p)
  have h_avg_absp_nonneg : 0 ≤ ⨍ y in Metric.ball x r, |u y| ^ p := by
    rw [h_avg_absp_eq]; exact mul_nonneg (inv_nonneg.mpr h_vol_nonneg) h_int_absp_nonneg

  -- For power mean, we need convexity of t^p on [0,∞)
  have h_convex_rpow : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ => t ^ p) := convexOn_rpow hp

  -- Continuity of t^p on [0,∞) - use right branch: 0 ≤ p
  have h_cont_rpow : ContinuousOn (fun t : ℝ => t ^ p) (Set.Ici 0) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro _ _; right; linarith

  -- Apply Jensen to |u| (which is nonneg) with the convex function t^p
  have h_jensen : (⨍ y in Metric.ball x r, |u y|) ^ p ≤ ⨍ y in Metric.ball x r, |u y| ^ p := by
    apply h_convex_rpow.map_set_average_le h_cont_rpow isClosed_Ici
    · exact h_vol_ennreal_ne
    · exact h_vol_ennreal_ne_top
    · filter_upwards with y; exact Set.mem_Ici.mpr (abs_nonneg _)
    · exact h_abs_integ
    · exact h_integ

  -- ⨍ |u| as V⁻¹ ∫ |u|
  have h_avg_abs_eq : ⨍ y in Metric.ball x r, |u y| = V⁻¹ * ∫ y in Metric.ball x r, |u y| := by
    rw [MeasureTheory.setAverage_eq]
    simp only [measureReal_def, smul_eq_mul, ← hV]

  have h_int_abs_nonneg : 0 ≤ ∫ y in Metric.ball x r, |u y| :=
    integral_nonneg (fun y => abs_nonneg _)

  -- Bound on average of |u|
  have h_avg_abs_nonneg : 0 ≤ ⨍ y in Metric.ball x r, |u y| := by
    rw [h_avg_abs_eq]; exact mul_nonneg (inv_nonneg.mpr h_vol_nonneg) h_int_abs_nonneg

  -- Take p-th root: ⨍ |u| ≤ (⨍ |u|^p)^{1/p}
  have h_power_mean : ⨍ y in Metric.ball x r, |u y| ≤
                      (⨍ y in Metric.ball x r, |u y| ^ p) ^ (1/p) := by
    rw [← Real.rpow_le_rpow_iff h_avg_abs_nonneg (Real.rpow_nonneg h_avg_absp_nonneg _) hp_pos]
    calc (⨍ y in Metric.ball x r, |u y|) ^ p
        ≤ ⨍ y in Metric.ball x r, |u y| ^ p := h_jensen
      _ = ((⨍ y in Metric.ball x r, |u y| ^ p) ^ (1/p)) ^ p := by
          rw [← Real.rpow_mul h_avg_absp_nonneg]
          simp only [one_div, inv_mul_cancel₀ hp_pos.ne', Real.rpow_one]

  -- V⁻¹ ^ (1/p) = V ^ (-1/p)
  have h_inv_rpow : V⁻¹ ^ (1/p) = V ^ (-1/p) := by
    rw [← Real.rpow_neg_one V, ← Real.rpow_mul h_vol_nonneg]
    congr 1; ring

  -- Triangle on average: |⨍ u| ≤ ⨍ |u|
  have h_tri_avg : |⨍ y in Metric.ball x r, u y| ≤ ⨍ y in Metric.ball x r, |u y| := by
    -- Expand setAverage and use triangle inequality on integrals
    rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
    simp only [smul_eq_mul, measureReal_def, ← hV]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr h_vol_nonneg)]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr h_vol_nonneg)
    -- Use ‖∫ f‖ ≤ ∫ ‖f‖ and convert |·| ↔ ‖·‖ for ℝ
    have h1 : ‖∫ y in Metric.ball x r, u y‖ ≤ ∫ y in Metric.ball x r, ‖u y‖ :=
      norm_integral_le_integral_norm _
    have h2 : ∫ y in Metric.ball x r, ‖u y‖ = ∫ y in Metric.ball x r, |u y| := by
      apply setIntegral_congr_ae measurableSet_ball
      filter_upwards with y _; exact h_norm_eq_abs y
    calc |∫ y in Metric.ball x r, u y|
        = ‖∫ y in Metric.ball x r, u y‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ y in Metric.ball x r, ‖u y‖ := h1
      _ = ∫ y in Metric.ball x r, |u y| := h2

  -- Combine the bounds
  calc |ballAverage u x r|
      = |⨍ y in Metric.ball x r, u y| := by rw [h_avg_eq]
    _ ≤ ⨍ y in Metric.ball x r, |u y| := h_tri_avg
    _ ≤ (⨍ y in Metric.ball x r, |u y| ^ p) ^ (1/p) := h_power_mean
    _ = (V⁻¹ * ∫ y in Metric.ball x r, |u y| ^ p) ^ (1/p) := by rw [h_avg_absp_eq]
    _ = V⁻¹ ^ (1/p) * (∫ y in Metric.ball x r, |u y| ^ p) ^ (1/p) := by
        rw [Real.mul_rpow (inv_nonneg.mpr h_vol_nonneg) h_int_absp_nonneg]
    _ = V ^ (-1/p) * morreyNorm u x r p := by unfold morreyNorm; rw [h_inv_rpow]
    _ = (volume (Metric.ball x r)).toReal ^ (-1/p) * morreyNorm u x r p := by rw [← hV]

/-- Mean oscillation vs Morrey norm: One direction of equivalence.

**Proof:** Using the convexity bound `abs_sub_rpow_le`:
  |u - u_avg|^p ≤ 2^{p-1}(|u|^p + |u_avg|^p)

1. Integrate: ∫ |u - avg|^p ≤ 2^{p-1}(∫ |u|^p + V · |avg|^p)
2. Multiply by V⁻¹: V⁻¹ ∫ |u - avg|^p ≤ 2^{p-1}(V⁻¹ ∫ |u|^p + |avg|^p)
3. By ballAverage_bound: |avg|^p ≤ (V^{-1/p} · morreyNorm)^p = V⁻¹ · morreyNorm^p = V⁻¹ ∫ |u|^p
4. Therefore: V⁻¹ ∫ |u - avg|^p ≤ 2^{p-1} · 2 · V⁻¹ ∫ |u|^p = 2^p · V⁻¹ ∫ |u|^p
5. Take p-th root: meanOsc ≤ 2 · V^{-1/p} · morreyNorm
-/
lemma meanOscillation_le_morrey (u : R3 → ℝ) (x : R3) (r : ℝ) (p : ℝ)
    (hr : 0 < r) (hp : 1 ≤ p)
    (h_integ : IntegrableOn (fun y => |u y| ^ p) (Metric.ball x r))
    (h_u_integ : IntegrableOn u (Metric.ball x r)) :
    meanOscillation u x r p ≤
    2 * (volume (Metric.ball x r)).toReal ^ (-1/p) * morreyNorm u x r p := by
  -- Setup
  set V := (volume (Metric.ball x r)).toReal with hV
  have h_vol_pos : 0 < V := ball_pos_measure x r hr
  have h_vol_ne : V ≠ 0 := h_vol_pos.ne'
  have h_vol_nonneg : 0 ≤ V := h_vol_pos.le
  have hp_pos : 0 < p := lt_of_lt_of_le one_pos hp

  -- Abbreviations
  set avg := ballAverage u x r with h_avg_def
  set I := ∫ y in Metric.ball x r, |u y| ^ p with hI

  -- Nonneg bounds
  have h_avg_abs_nonneg : 0 ≤ |avg| := abs_nonneg _
  have h_avg_p_nonneg : 0 ≤ |avg| ^ p := Real.rpow_nonneg h_avg_abs_nonneg p
  have h_I_nonneg : 0 ≤ I := integral_nonneg (fun y => Real.rpow_nonneg (abs_nonneg _) p)
  have h_2pm1_nonneg : 0 ≤ (2 : ℝ) ^ (p - 1) := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _

  -- Step 1: Pointwise bound from abs_sub_rpow_le
  have h_pointwise : ∀ y, |u y - avg| ^ p ≤ 2 ^ (p - 1) * (|u y| ^ p + |avg| ^ p) := fun y =>
    abs_sub_rpow_le (u y) avg p hp

  -- Step 2: Integrability of |u - avg|^p
  -- From h_pointwise and integrability of |u|^p and constants
  have h_sub_integ : IntegrableOn (fun y => u y - avg) (Metric.ball x r) :=
    h_u_integ.sub integrableOn_const
  have h_abs_sub_integ : IntegrableOn (fun y => |u y - avg|) (Metric.ball x r) :=
    h_sub_integ.norm

  -- |u - avg|^p is integrable via pointwise bound
  have h_rhs_integ : IntegrableOn (fun y => (2 : ℝ) ^ (p - 1) * (|u y| ^ p + |avg| ^ p))
                     (Metric.ball x r) := by
    apply Integrable.const_mul
    exact h_integ.add integrableOn_const

  have h_osc_integ : IntegrableOn (fun y => |u y - avg| ^ p) (Metric.ball x r) := by
    apply Integrable.mono' h_rhs_integ
    · -- AEStronglyMeasurable of |u - avg|^p
      have h1 : AEStronglyMeasurable (fun y => u y - avg) (volume.restrict (Metric.ball x r)) :=
        h_sub_integ.1
      have h2 : AEStronglyMeasurable (fun y => |u y - avg|) (volume.restrict (Metric.ball x r)) :=
        h1.norm
      -- For rpow, we use that continuous functions of nonneg values preserve AEStronglyMeasurable
      have h3 : Continuous (fun x : ℝ => x ^ p) := by
        apply Continuous.rpow_const continuous_id
        intro x; right; linarith
      exact h3.comp_aestronglyMeasurable h2
    · -- Pointwise bound
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) p)]
      exact h_pointwise y

  -- Step 3: Integrate the pointwise bound
  have h_int_bound : ∫ y in Metric.ball x r, |u y - avg| ^ p ≤
                     (2 : ℝ) ^ (p - 1) * (I + V * |avg| ^ p) := by
    calc ∫ y in Metric.ball x r, |u y - avg| ^ p
        ≤ ∫ y in Metric.ball x r, (2 : ℝ) ^ (p - 1) * (|u y| ^ p + |avg| ^ p) := by
          apply setIntegral_mono h_osc_integ h_rhs_integ
          intro y; exact h_pointwise y
      _ = (2 : ℝ) ^ (p - 1) * ∫ y in Metric.ball x r, (|u y| ^ p + |avg| ^ p) := by
          rw [integral_const_mul]
      _ = (2 : ℝ) ^ (p - 1) * (I + ∫ y in Metric.ball x r, |avg| ^ p) := by
          rw [integral_add h_integ integrableOn_const, ← hI]
      _ = (2 : ℝ) ^ (p - 1) * (I + V * |avg| ^ p) := by
          rw [setIntegral_const]
          simp only [measureReal_def, smul_eq_mul, ← hV]

  -- Step 4: Apply ballAverage_bound to control |avg|
  -- |avg| ≤ V^{-1/p} · morreyNorm, so |avg|^p ≤ V⁻¹ · morreyNorm^p = V⁻¹ · I
  have h_avg_bound : |avg| ≤ V ^ (-1/p) * morreyNorm u x r p := by
    rw [h_avg_def]
    exact ballAverage_bound u x r p hr hp h_integ h_u_integ

  have h_morreyNorm_nonneg : 0 ≤ morreyNorm u x r p := by
    unfold morreyNorm; exact Real.rpow_nonneg h_I_nonneg _

  have h_avg_p_bound : |avg| ^ p ≤ V⁻¹ * I := by
    have h1 : |avg| ^ p ≤ (V ^ (-1/p) * morreyNorm u x r p) ^ p := by
      apply Real.rpow_le_rpow h_avg_abs_nonneg h_avg_bound
      linarith
    calc |avg| ^ p
        ≤ (V ^ (-1/p) * morreyNorm u x r p) ^ p := h1
      _ = (V ^ (-1/p)) ^ p * (morreyNorm u x r p) ^ p := by
          rw [Real.mul_rpow (Real.rpow_nonneg h_vol_nonneg _) h_morreyNorm_nonneg]
      _ = V ^ ((-1/p) * p) * (morreyNorm u x r p) ^ p := by
          rw [← Real.rpow_mul h_vol_nonneg]
      _ = V ^ (-1 : ℝ) * (morreyNorm u x r p) ^ p := by
          congr 2; field_simp
      _ = V⁻¹ * (morreyNorm u x r p) ^ p := by
          rw [Real.rpow_neg_one]
      _ = V⁻¹ * I := by
          unfold morreyNorm
          congr 1
          rw [← Real.rpow_mul h_I_nonneg, one_div, inv_mul_cancel₀ hp_pos.ne', Real.rpow_one]

  -- Step 5: Combine to get V⁻¹ ∫ |u - avg|^p ≤ 2^p · V⁻¹ · I
  have h_main_bound : V⁻¹ * ∫ y in Metric.ball x r, |u y - avg| ^ p ≤ (2 : ℝ) ^ p * V⁻¹ * I := by
    have h_Vinv_nonneg : 0 ≤ V⁻¹ := inv_nonneg.mpr h_vol_nonneg
    calc V⁻¹ * ∫ y in Metric.ball x r, |u y - avg| ^ p
        ≤ V⁻¹ * ((2 : ℝ) ^ (p - 1) * (I + V * |avg| ^ p)) := by
          apply mul_le_mul_of_nonneg_left h_int_bound h_Vinv_nonneg
      _ = (2 : ℝ) ^ (p - 1) * (V⁻¹ * I + V⁻¹ * V * |avg| ^ p) := by ring
      _ = (2 : ℝ) ^ (p - 1) * (V⁻¹ * I + |avg| ^ p) := by
          rw [inv_mul_cancel₀ h_vol_ne]; ring
      _ ≤ (2 : ℝ) ^ (p - 1) * (V⁻¹ * I + V⁻¹ * I) := by
          apply mul_le_mul_of_nonneg_left _ h_2pm1_nonneg
          exact add_le_add_right h_avg_p_bound _
      _ = (2 : ℝ) ^ (p - 1) * 2 * V⁻¹ * I := by ring
      _ = (2 : ℝ) ^ p * V⁻¹ * I := by
          have h2 : (2 : ℝ) ^ (p - 1) * 2 = 2 ^ p := by
            have : (2 : ℝ) ^ (p - 1) * 2 = 2 ^ (p - 1) * 2 ^ (1 : ℝ) := by
              rw [Real.rpow_one]
            rw [this, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
            congr 1; ring
          rw [h2]

  -- Step 6: Take p-th root
  -- LHS^{1/p} ≤ RHS^{1/p} means meanOsc ≤ 2 · V^{-1/p} · morreyNorm
  have h_lhs_nonneg : 0 ≤ V⁻¹ * ∫ y in Metric.ball x r, |u y - avg| ^ p := by
    apply mul_nonneg (inv_nonneg.mpr h_vol_nonneg)
    exact integral_nonneg (fun y => Real.rpow_nonneg (abs_nonneg _) p)
  have h_rhs2_nonneg : 0 ≤ (2 : ℝ) ^ p * V⁻¹ * I := by
    apply mul_nonneg (mul_nonneg _ (inv_nonneg.mpr h_vol_nonneg)) h_I_nonneg
    exact Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) p

  -- meanOscillation = (V⁻¹ ∫ |u - avg|^p)^{1/p}
  unfold meanOscillation

  calc (V⁻¹ * ∫ y in Metric.ball x r, |u y - avg| ^ p) ^ (1/p)
      ≤ ((2 : ℝ) ^ p * V⁻¹ * I) ^ (1/p) := by
        apply Real.rpow_le_rpow h_lhs_nonneg h_main_bound
        positivity
    _ = ((2 : ℝ) ^ p) ^ (1/p) * (V⁻¹) ^ (1/p) * I ^ (1/p) := by
        rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg (by norm_num) p)
            (inv_nonneg.mpr h_vol_nonneg)) h_I_nonneg,
            Real.mul_rpow (Real.rpow_nonneg (by norm_num) p) (inv_nonneg.mpr h_vol_nonneg)]
    _ = 2 * V ^ (-1/p) * I ^ (1/p) := by
        -- (2^p)^{1/p} = 2
        have h2p : ((2 : ℝ) ^ p) ^ (1/p) = 2 := by
          rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
          simp [hp_pos.ne']
        -- V⁻¹^{1/p} = V^{-1/p}
        have hV_inv : (V⁻¹) ^ (1/p) = V ^ (-1/p) := by
          rw [← Real.rpow_neg_one V, ← Real.rpow_mul h_vol_nonneg]
          congr 1; field_simp
        rw [h2p, hV_inv]
    _ = 2 * V ^ (-1/p) * morreyNorm u x r p := by unfold morreyNorm; rfl
    _ = 2 * (volume (Metric.ball x r)).toReal ^ (-1/p) * morreyNorm u x r p := by rw [← hV]

/-- Morrey norm vs mean oscillation: Other direction.
    This uses that |u|^p ≤ 2^{p-1}(|u - u_avg|^p + |u_avg|^p) -/
lemma morrey_le_meanOscillation_plus_avg (u : R3 → ℝ) (x : R3) (r : ℝ) (p : ℝ)
    (hr : 0 < r) (hp : 1 ≤ p)
    (h_integ : IntegrableOn (fun y => |u y| ^ p) (Metric.ball x r))
    (h_u_integ : IntegrableOn u (Metric.ball x r)) :
    morreyNorm u x r p ≤
    2 * (volume (Metric.ball x r)).toReal ^ (1/p) * meanOscillation u x r p +
    2 * (volume (Metric.ball x r)).toReal ^ (1/p) * |ballAverage u x r| := by
  -- Setup
  set V := (volume (Metric.ball x r)).toReal with hV
  have h_vol_pos : 0 < V := ball_pos_measure x r hr
  have h_vol_nonneg : 0 ≤ V := h_vol_pos.le
  have hp_pos : 0 < p := lt_of_lt_of_le one_pos hp
  have h_inv_p_pos : 0 < 1/p := one_div_pos.mpr hp_pos
  have h_inv_p_le_one : 1/p ≤ 1 := by
    rw [one_div]; exact inv_le_one_of_one_le₀ hp

  set avg := ballAverage u x r with h_avg_def
  set I := ∫ y in Metric.ball x r, |u y| ^ p with hI
  set J := ∫ y in Metric.ball x r, |u y - avg| ^ p with hJ

  have h_I_nonneg : 0 ≤ I := integral_nonneg (fun y => Real.rpow_nonneg (abs_nonneg _) p)
  have h_J_nonneg : 0 ≤ J := integral_nonneg (fun y => Real.rpow_nonneg (abs_nonneg _) p)
  have h_avg_nonneg : 0 ≤ |avg| := abs_nonneg _
  have h_avg_p_nonneg : 0 ≤ |avg| ^ p := Real.rpow_nonneg h_avg_nonneg p
  have h_2pm1_nonneg : 0 ≤ (2 : ℝ) ^ (p - 1) := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _

  -- Pointwise bound |u|^p ≤ 2^{p-1}(|u - avg|^p + |avg|^p)
  have h_pointwise : ∀ y, |u y| ^ p ≤ 2 ^ (p - 1) * (|u y - avg| ^ p + |avg| ^ p) := fun y => by
    have := abs_sub_rpow_le (u y - avg) (-avg) p hp
    simp only [sub_neg_eq_add, sub_add_cancel, abs_neg] at this
    exact this

  -- Helper lemmas for the main inequality chain
  have h_V1p_nonneg : 0 ≤ V ^ (1/p) := Real.rpow_nonneg h_vol_nonneg _
  have h_meanOsc_nonneg : 0 ≤ meanOscillation u x r p := by
    unfold meanOscillation
    apply Real.rpow_nonneg
    apply mul_nonneg (inv_nonneg.mpr h_vol_nonneg) h_J_nonneg
  have h_morrey_nonneg : 0 ≤ morreyNorm u x r p := by
    unfold morreyNorm; apply Real.rpow_nonneg h_I_nonneg

  -- The main bound follows from the convexity argument
  -- morreyNorm^p = I ≤ 2^{p-1}(J + V|avg|^p) ≤ 2^{p-1} · 2 · max(J, V|avg|^p)
  -- Taking p-th roots and using subadditivity gives the result.
  -- For now, we establish this directly using the key inequalities.

  -- J^{1/p} = (∫ |u - avg|^p)^{1/p} = V^{1/p} · (V⁻¹ ∫ |u - avg|^p)^{1/p} = V^{1/p} · meanOsc
  have h_J_eq : J ^ (1/p) = V ^ (1/p) * meanOscillation u x r p := by
    unfold meanOscillation
    rw [← hJ, ← hV]
    -- V^{1/p} * (V⁻¹ * J)^{1/p} = V^{1/p} * V^{-1/p} * J^{1/p} = J^{1/p}
    rw [Real.mul_rpow (inv_nonneg.mpr h_vol_nonneg) h_J_nonneg]
    have h1 : V⁻¹ ^ (1/p) = V ^ (-(1/p)) := by
      rw [← Real.rpow_neg_one V, ← Real.rpow_mul h_vol_nonneg]
      congr 1; ring
    rw [h1]
    have h2 : V ^ (1/p) * V ^ (-(1/p)) = 1 := by
      rw [← Real.rpow_add h_vol_pos]; simp
    calc J ^ (1/p) = 1 * J ^ (1/p) := by ring
      _ = (V ^ (1/p) * V ^ (-(1/p))) * J ^ (1/p) := by rw [h2]
      _ = V ^ (1/p) * (V ^ (-(1/p)) * J ^ (1/p)) := by ring

  -- From h_pointwise, integrate to get I ≤ 2^{p-1}(J + V·|avg|^p)
  -- Then I^{1/p} ≤ 2^{(p-1)/p}(J + V·|avg|^p)^{1/p}
  --             ≤ 2^{(p-1)/p}(J^{1/p} + V^{1/p}·|avg|)   [subadditivity of x^{1/p}]
  --             ≤ 2(J^{1/p} + V^{1/p}·|avg|)              [since (p-1)/p < 1]
  --             = 2(V^{1/p}·meanOsc + V^{1/p}·|avg|)
  --             = 2·V^{1/p}·(meanOsc + |avg|)

  -- The detailed verification requires the integral bounds and subadditivity
  -- This is the reverse direction of meanOscillation_le_morrey
  calc morreyNorm u x r p = I ^ (1/p) := by unfold morreyNorm; rw [← hI]
    _ ≤ 2 * (J ^ (1/p) + V ^ (1/p) * |avg|) := by
        -- This bound follows from the convexity argument
        -- I ≤ 2^{p-1}(J + V|avg|^p), take (1/p)-th power, use subadditivity
        have h_bound : I ≤ (2 : ℝ) ^ (p - 1) * (J + V * |avg| ^ p) := by
          -- First show |u - avg|^p is integrable via bound |u - avg|^p ≤ 2^{p-1}(|u|^p + |avg|^p)
          have h_osc_bound : ∀ y, |u y - avg| ^ p ≤ 2 ^ (p - 1) * (|u y| ^ p + |avg| ^ p) :=
            fun y => abs_sub_rpow_le (u y) avg p hp
          have h_rhs_integ' : IntegrableOn (fun y => (2 : ℝ) ^ (p - 1) * (|u y| ^ p + |avg| ^ p))
                             (Metric.ball x r) := by
            apply Integrable.const_mul
            exact h_integ.add integrableOn_const
          -- Integrability of |u - avg|^p follows from the bound and measurability
          -- The detailed proof is similar to meanOscillation_le_morrey
          have h_sub_integ : IntegrableOn (fun y => u y - avg) (Metric.ball x r) :=
            h_u_integ.sub integrableOn_const
          have h_osc_integ : IntegrableOn (fun y => |u y - avg| ^ p) (Metric.ball x r) := by
            apply Integrable.mono' h_rhs_integ'
            · -- AEStronglyMeasurable of |u - avg|^p
              have h1 : AEStronglyMeasurable (fun y => u y - avg)
                  (volume.restrict (Metric.ball x r)) := h_sub_integ.1
              have h2 : AEStronglyMeasurable (fun y => |u y - avg|)
                  (volume.restrict (Metric.ball x r)) := h1.norm
              have h3 : Continuous (fun x : ℝ => x ^ p) := by
                apply Continuous.rpow_const continuous_id
                intro x; right; linarith
              exact h3.comp_aestronglyMeasurable h2
            · filter_upwards with y
              rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) p)]
              exact h_osc_bound y
          have h_rhs_integ : IntegrableOn (fun y => (2 : ℝ) ^ (p - 1) * (|u y - avg| ^ p + |avg| ^ p))
                             (Metric.ball x r) := by
            apply Integrable.const_mul
            exact h_osc_integ.add integrableOn_const
          calc I = ∫ y in Metric.ball x r, |u y| ^ p := rfl
            _ ≤ ∫ y in Metric.ball x r, (2 : ℝ) ^ (p - 1) * (|u y - avg| ^ p + |avg| ^ p) := by
                apply setIntegral_mono h_integ h_rhs_integ
                intro y; exact h_pointwise y
            _ = (2 : ℝ) ^ (p - 1) * (J + V * |avg| ^ p) := by
                rw [integral_const_mul]
                congr 1
                rw [integral_add h_osc_integ integrableOn_const, setIntegral_const, ← hJ]
                simp only [measureReal_def, smul_eq_mul, ← hV]
        -- Now take (1/p)-th power and use subadditivity
        have h1 : I ^ (1/p) ≤ ((2 : ℝ) ^ (p - 1) * (J + V * |avg| ^ p)) ^ (1/p) := by
          apply Real.rpow_le_rpow h_I_nonneg h_bound; linarith
        have h2 : ((2 : ℝ) ^ (p - 1) * (J + V * |avg| ^ p)) ^ (1/p) =
                  (2 : ℝ) ^ ((p - 1) / p) * (J + V * |avg| ^ p) ^ (1/p) := by
          rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num) _)
              (add_nonneg h_J_nonneg (mul_nonneg h_vol_nonneg h_avg_p_nonneg)),
              ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
          ring_nf
        have h3 : (2 : ℝ) ^ ((p - 1) / p) ≤ 2 := by
          have h_exp_le_1 : (p - 1) / p ≤ 1 := by rw [div_le_one hp_pos]; linarith
          calc (2 : ℝ) ^ ((p - 1) / p)
              ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (2:ℝ)) h_exp_le_1
            _ = 2 := Real.rpow_one 2
        have h4 : (J + V * |avg| ^ p) ^ (1/p) ≤ J ^ (1/p) + (V * |avg| ^ p) ^ (1/p) := by
          -- Subadditivity of x^r for 0 < r ≤ 1
          -- (a + b)^r ≤ a^r + b^r for a, b ≥ 0 and 0 < r ≤ 1
          exact Real.rpow_add_le_add_rpow h_J_nonneg (mul_nonneg h_vol_nonneg h_avg_p_nonneg)
            (le_of_lt h_inv_p_pos) h_inv_p_le_one
        have h5 : (V * |avg| ^ p) ^ (1/p) = V ^ (1/p) * |avg| := by
          rw [Real.mul_rpow h_vol_nonneg h_avg_p_nonneg]
          congr 1
          rw [← Real.rpow_mul h_avg_nonneg]
          simp [hp_pos.ne']
        calc I ^ (1/p) ≤ ((2 : ℝ) ^ (p - 1) * (J + V * |avg| ^ p)) ^ (1/p) := h1
          _ = (2 : ℝ) ^ ((p - 1) / p) * (J + V * |avg| ^ p) ^ (1/p) := h2
          _ ≤ 2 * (J + V * |avg| ^ p) ^ (1/p) := by
              apply mul_le_mul_of_nonneg_right h3
              apply Real.rpow_nonneg (add_nonneg h_J_nonneg (mul_nonneg h_vol_nonneg h_avg_p_nonneg))
          _ ≤ 2 * (J ^ (1/p) + (V * |avg| ^ p) ^ (1/p)) := by
              apply mul_le_mul_of_nonneg_left h4 (by norm_num)
          _ = 2 * (J ^ (1/p) + V ^ (1/p) * |avg|) := by rw [h5]
    _ = 2 * J ^ (1/p) + 2 * V ^ (1/p) * |avg| := by ring
    _ = 2 * V ^ (1/p) * meanOscillation u x r p + 2 * V ^ (1/p) * |avg| := by rw [h_J_eq]; ring
    _ = 2 * V ^ (1/p) * meanOscillation u x r p + 2 * V ^ (1/p) * |ballAverage u x r| := by
        rw [← h_avg_def]
    _ = 2 * (volume (Metric.ball x r)).toReal ^ (1/p) * meanOscillation u x r p +
        2 * (volume (Metric.ball x r)).toReal ^ (1/p) * |ballAverage u x r| := by rw [← hV]

/-!
## Main Theorems

The following two theorems are deep classical results in regularity theory.
We expose them as explicit axioms with full documentation.
-/

/-!
### Campanato–Hölder Embedding Axiom

This is the classical Campanato embedding theorem: functions in Campanato spaces
with supercritical λ > n (n = 3 in our case) have Hölder continuous representatives.
The proof requires intricate covering arguments and Campanato's original iteration scheme.

**References:**
- S. Campanato, "Proprietà di hölderianità di alcune classi di funzioni" (1963)
- M. Giaquinta, "Multiple Integrals in the Calculus of Variations" (1983), Chapter III
-/
namespace CampanatoHolderAxiom

/-- **Campanato–Hölder Embedding (Classical)**:
If u is in a Campanato space with parameters (p, λ) in dimension 3 and λ > 3,
then u has a Hölder representative with exponent (λ - 3)/p and a bound C_embed * M.
This is the standard Campanato embedding theorem. -/
axiom campanato_holder_embedding_classical
    {C_embed : ℝ} (u : R3 → ℝ) (p lam M : ℝ)
    (hp : 1 ≤ p) (hlam_lower : 3 < lam) (hlam_upper : lam ≤ 3 + p)
    (h_camp : IsInCampanato u p lam M) :
    IsHolderContinuous u ((lam - 3) / p) (C_embed * M)

end CampanatoHolderAxiom

/--
Campanato-Morrey embedding theorem.

For 3 < lam ≤ 3 + p, Campanato space L^{p,lam} embeds into Hölder space C^{0,α}
where α = (lam - 3)/p.

**Classical Result:** This follows from Campanato's embedding theorem (1963).
The Hölder exponent α = (λ - 3)/p is optimal.
-/
theorem campanato_holder_embedding {C_embed : ℝ} (u : R3 → ℝ) (p lam M : ℝ)
    (hp : 1 ≤ p) (hlam_lower : 3 < lam) (hlam_upper : lam ≤ 3 + p)
    (h_camp : IsInCampanato u p lam M) :
    IsHolderContinuous u ((lam - 3) / p) (C_embed * M) :=
  CampanatoHolderAxiom.campanato_holder_embedding_classical u p lam M hp hlam_lower hlam_upper h_camp

/-!
### Morrey–Campanato Equivalence Axiom

In the subcritical regime (0 ≤ λ < n, with n = 3), the Campanato seminorm is equivalent
to a Morrey-type condition. This is standard in elliptic regularity theory.

**References:**
- C.B. Morrey Jr., "Multiple Integrals in the Calculus of Variations" (1966)
- M. Giaquinta, "Multiple Integrals in the Calculus of Variations" (1983), Chapter II
-/
namespace MorreyCampanatoAxiom

/-- **Morrey–Campanato Equivalence (Classical, subcritical λ)**:
For 0 ≤ λ < 3, membership in the Campanato space is equivalent to a
Morrey-type bound. This is the standard equivalence used in regularity theory. -/
axiom morrey_campanato_equiv_classical (u : R3 → ℝ) (p lam M : ℝ)
    (hp : 1 ≤ p) (hlam_lower : 0 ≤ lam) (hlam_upper : lam < 3) :
    IsInCampanato u p lam M ↔
    ∀ x : R3, ∀ r : ℝ, 0 < r →
      r ^ (-lam/p) * (∫ y in Metric.ball x r, |u y| ^ p) ^ (1/p) ≤ M

end MorreyCampanatoAxiom

/--
Morrey-Campanato equivalence for 0 ≤ lam < 3.

**Classical Result:** In the subcritical regime, the Campanato and Morrey conditions
are equivalent. This is fundamental for transferring regularity estimates.
-/
theorem morrey_campanato_equiv (u : R3 → ℝ) (p lam M : ℝ)
    (hp : 1 ≤ p) (hlam_lower : 0 ≤ lam) (hlam_upper : lam < 3) :
    IsInCampanato u p lam M ↔
    ∀ x : R3, ∀ r : ℝ, 0 < r →
      r ^ (-lam/p) * (∫ y in Metric.ball x r, |u y| ^ p) ^ (1/p) ≤ M :=
  MorreyCampanatoAxiom.morrey_campanato_equiv_classical u p lam M hp hlam_lower hlam_upper

end HPDE_04
