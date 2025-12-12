import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import HPDE_common.HPDE_common
import HPDE_01_caccioppoli.EllipticCaccioppoli

open Real MeasureTheory Set Metric

namespace HPDE_02

/-!
# Weighted Caccioppoli Inequality

An extension of the standard Caccioppoli inequality with power-type weights.

For weights of the form w(x) = |x|^α, we prove:
  ∫_{B_r} |x|^α |∇u|² ≤ C/(R-r)² ∫_{B_R} |x|^α u²

## References

- Fabes-Kenig-Serapioni (1982): Degenerate elliptic equations
- Heinonen-Kilpeläinen-Martio (2006): Nonlinear potential theory
-/

/-- R³ as Fin 3 → ℝ -/
abbrev R3 := Fin 3 → ℝ

/-- Power weight |x|^α -/
noncomputable def powerWeight (α : ℝ) (x : R3) : ℝ := ‖x‖ ^ α

/-!
## Power Weight Properties
-/

/-- Power weight is positive when x ≠ 0 -/
lemma powerWeight_pos {α : ℝ} {x : R3} (hx : x ≠ 0) :
    0 < powerWeight α x := by
  unfold powerWeight
  exact Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) α

/-- Power weight at 0 is 0 for α > 0 -/
lemma powerWeight_zero {α : ℝ} (hα : 0 < α) :
    powerWeight α 0 = 0 := by
  unfold powerWeight
  simp [Real.zero_rpow hα.ne']

/-- Power weight with α = 0 is constant 1 -/
lemma powerWeight_zero_exp (x : R3) :
    powerWeight 0 x = 1 := by
  unfold powerWeight
  exact Real.rpow_zero ‖x‖

/-- Power weight product rule (for nonzero x) -/
lemma powerWeight_add (α β : ℝ) {x : R3} (hx : x ≠ 0) :
    powerWeight α x * powerWeight β x = powerWeight (α + β) x := by
  unfold powerWeight
  exact (Real.rpow_add (norm_pos_iff.mpr hx) α β).symm

/-- Power weight inverse (hx ensures well-definedness for negative α) -/
lemma powerWeight_neg (α : ℝ) {x : R3} (_hx : x ≠ 0) :
    (powerWeight α x)⁻¹ = powerWeight (-α) x := by
  unfold powerWeight
  rw [Real.rpow_neg (norm_nonneg x)]

/-- Power weight scaling: |λx|^α = |λ|^α |x|^α for λ ≥ 0 -/
lemma powerWeight_smul (α : ℝ) (c : ℝ) (hc : 0 ≤ c) (x : R3) :
    powerWeight α (c • x) = c ^ α * powerWeight α x := by
  unfold powerWeight
  rw [norm_smul, Real.norm_of_nonneg hc, Real.mul_rpow hc (norm_nonneg x)]

/-- Muckenhoupt A_2 condition for a weight -/
def IsMuckenhouptA2 (w : R3 → ℝ) : Prop :=
  ∃ C > 0, ∀ (x : R3) (r : ℝ), 0 < r →
    ((volume (Metric.ball x r)).toReal⁻¹ * ∫ y in Metric.ball x r, w y) *
    ((volume (Metric.ball x r)).toReal⁻¹ * ∫ y in Metric.ball x r, (w y)⁻¹) ≤ C

/-- The constant weight 1 is trivially A₂.
    Both averages equal 1, so product = 1 ≤ 1. -/
lemma weight_one_is_A2 : IsMuckenhouptA2 (fun _ : R3 => (1 : ℝ)) := by
  use 1
  constructor
  · exact one_pos
  · intro x r hr
    -- Both integrals of 1 over B_r equal volume(B_r)
    -- So average of 1 = 1, and 1⁻¹ = 1
    have h_vol_pos : 0 < (volume (Metric.ball x r)).toReal := by
      apply ENNReal.toReal_pos
      · exact (Metric.measure_ball_pos volume x hr).ne'
      · exact measure_ball_lt_top.ne
    have h_int_one : ∫ y in Metric.ball x r, (1 : ℝ) = (volume (Metric.ball x r)).toReal := by
      rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_one]
    have h_int_inv : ∫ y in Metric.ball x r, (1 : ℝ)⁻¹ = (volume (Metric.ball x r)).toReal := by
      simp only [inv_one]
      rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_one]
    rw [h_int_one, h_int_inv]
    -- Now: (vol⁻¹ * vol) * (vol⁻¹ * vol) = 1 * 1 = 1
    have h1 : (volume (Metric.ball x r)).toReal⁻¹ * (volume (Metric.ball x r)).toReal = 1 :=
      inv_mul_cancel₀ h_vol_pos.ne'
    simp only [h1, one_mul, le_refl]

/-- powerWeight 0 = 1, so it's A₂ -/
lemma powerWeight_zero_A2 : IsMuckenhouptA2 (powerWeight 0) := by
  -- powerWeight 0 x = ‖x‖^0 = 1 for all x
  have h_eq : (powerWeight 0) = (fun _ : R3 => (1 : ℝ)) := by
    ext x
    exact powerWeight_zero_exp x
  rw [h_eq]
  exact weight_one_is_A2

/-!
## Classical A₂ Result for Power Weights

The following axiom encapsulates a deep classical result from harmonic analysis:
the power weight |x|^α satisfies the Muckenhoupt A₂ condition in ℝⁿ precisely
when -n < α < n.

### Mathematical Background

The A₂ condition states: there exists C > 0 such that for all balls B,
  (|B|⁻¹ ∫_B w) × (|B|⁻¹ ∫_B w⁻¹) ≤ C

For power weights w(x) = |x|^α in ℝ³:

**Case 1: Ball far from origin** (‖center‖ ≥ 2r)
- The weight is approximately constant on the ball
- Product of averages ≈ w(x) × w(x)⁻¹ = 1

**Case 2: Ball near/containing origin** (‖center‖ < 2r)
- Use radial integration: ∫_{B(0,R)} |y|^β dy = (4π/(3+β)) × R^{3+β} for β > -3
- Average of |·|^α over B(0,R) scales as R^α
- Product of averages for α and -α: bounded by 9/(9-α²) × geometric factor

The condition -3 < α < 3 ensures both |·|^α and |·|^{-α} are locally integrable
in ℝ³, which is necessary and sufficient for the A₂ property.

### References
- Muckenhoupt, B. (1972). "Weighted norm inequalities for the Hardy maximal function"
- Fabes, E., Kenig, C., Serapioni, R. (1982). "The local regularity of solutions
  of degenerate elliptic equations"
- Heinonen, J., Kilpeläinen, T., Martio, O. (2006). "Nonlinear Potential Theory
  of Degenerate Elliptic Equations"
-/

namespace PowerWeightA2Axiom

/-- Classical result: power weights satisfy Muckenhoupt A₂ in dimension 3.

This is a deep result from harmonic analysis that requires spherical coordinate
integration and careful analysis of radial integrals near the origin.
We accept it as an axiom for this formalization. -/
axiom powerWeight_A2_classical {α : ℝ} (hα : -3 < α ∧ α < 3) :
    IsMuckenhouptA2 (powerWeight α)

end PowerWeightA2Axiom

/-- Power weight satisfies A_2 condition for -3 < α < 3.

This follows from the classical result `powerWeight_A2_classical`.
See the documentation above for the mathematical background and references. -/
lemma powerWeight_A2 {α : ℝ} (hα : -3 < α ∧ α < 3) :
    IsMuckenhouptA2 (powerWeight α) :=
  PowerWeightA2Axiom.powerWeight_A2_classical hα

/-- A function is weakly harmonic in a weighted sense.

For a weight w, this means: ∫ w(x) ∇u · ∇φ dx = 0 for all test functions φ.
The integral uses the coordinate-sum form of the inner product of gradients:
  ∇u · ∇φ = ∑ᵢ (∂u/∂xᵢ)(∂φ/∂xᵢ)
-/
def IsWeightedHarmonicOn (u : R3 → ℝ) (w : R3 → ℝ) (R : ℝ) : Prop :=
  ∀ φ : R3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → (∀ x, x ∉ Metric.ball (0 : R3) R → φ x = 0) →
    ∫ x in Metric.closedBall (0 : R3) R,
      w x * ∑ i : Fin 3, (fderiv ℝ u x) (Pi.single i 1) * (fderiv ℝ φ x) (Pi.single i 1) = 0

/-!
## Helper: Weighted gradientSq
-/

/-- Weighted squared gradient: w(x) · |∇f(x)|² -/
noncomputable def weightedGradientSq (w : R3 → ℝ) (f : R3 → ℝ) (x : R3) : ℝ :=
  w x * HPDE_01.gradientSq f x

/-!
## Main Theorem
-/

/--
The weighted Caccioppoli inequality.

For a weakly harmonic function u with weight w satisfying A_2:
  ∫_{B_r} w |∇u|² ≤ C/(R-r)² ∫_{B_R} w u²

The proof follows the same absorption pattern as the unweighted case:
1. Test weak form with φ = η²u
2. Get identity: ∫ w·η²·|∇u|² + 2∫ w·η·u·∇u·∇η = 0
3. Apply Young's inequality to cross term
4. Use absorption_from_cross_bound to conclude
-/
theorem weighted_caccioppoli (u : R3 → ℝ) (w : R3 → ℝ) (R r : ℝ)
    (hR : 0 < R) (hr : 0 < r) (hrR : r < R)
    (hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (hw_nonneg : ∀ x, 0 ≤ w x)
    (hw_meas : Measurable w)
    (h_harmonic : IsWeightedHarmonicOn u w R)
    (h_w_u_integ : IntegrableOn (fun x => w x * (u x)^2) (Metric.closedBall 0 R) volume)
    (h_w_gradSq_integ : IntegrableOn (fun x => weightedGradientSq w u x) (Metric.closedBall 0 R) volume) :
    ∃ C > 0, ∫ x in Metric.closedBall (0 : R3) r, weightedGradientSq w u x ≤
      C / (R - r)^2 * ∫ x in Metric.closedBall (0 : R3) R, w x * (u x)^2 := by
  /-
  PROOF STRUCTURE (mirrors HPDE-01 caccioppoli_elliptic_gradSq with weight w):

  1. Get smooth cutoff η with η=1 on B_r, η=0 outside B_R, ‖∇η‖ ≤ C₀/(R-r)
  2. Test weighted weak form with φ = η²u:
     ∫ w · ∑ᵢ (∂ᵢu)(∂ᵢ(η²u)) = 0
  3. Expand using product rule:
     ∑ᵢ (∂ᵢu)(∂ᵢ(η²u)) = 2ηu·⟨∇u,∇η⟩ + η²·gradientSq u
  4. So: ∫ w·η²·gradientSq u + 2·∫ w·ηu·⟨∇u,∇η⟩ = 0
     This is the form: ∫A + 2∫B = 0
  5. Apply Young's inequality: |2·w·ηu·⟨∇u,∇η⟩| ≤ (1/2)·w·η²·gradSq u + 2·w·u²·gradSq η
     This gives: |2B| ≤ (1/2)A + 2C pointwise
  6. Apply absorption_from_cross_bound: ∫A ≤ 4∫C
  7. Chain with gradient bound: gradSq η ≤ 3·C₀²/(R-r)²
     Final: ∫ w·η²·gradSq u ≤ 12·C₀²/(R-r)² · ∫ w·u²
  8. Restrict to inner ball (η=1 on B_r)
  -/

  -- Step 1: Get cutoff function
  obtain ⟨η, h_smooth, h_one, h_zero, h_bounds, C₀, hC₀_pos, h_grad_bound⟩ :=
    HPDE_common.exists_smooth_cutoff_ball r R hr hrR

  -- Step 2: Test function validity
  let φ := fun y : R3 => (η y)^2 * u y
  have hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ := (h_smooth.pow 2).mul hu_smooth
  have hφ_support : ∀ x, x ∉ Metric.ball (0 : R3) R → φ x = 0 := fun x hx => by
    have hη0 : η x = 0 := h_zero x hx
    show (η x)^2 * u x = 0
    rw [hη0, sq, zero_mul, zero_mul]

  -- Step 3: Weighted weak harmonicity
  have h_weak : ∫ x in Metric.closedBall (0 : R3) R,
      w x * ∑ i : Fin 3, (fderiv ℝ u x) (Pi.single i 1) * (fderiv ℝ φ x) (Pi.single i 1) = 0 :=
    h_harmonic φ hφ_smooth hφ_support

  -- Step 4-7: Absorption argument (main technical content)
  -- This uses the same absorption_from_cross_bound as HPDE-01
  -- but with weighted functions A, B, C
  have h_absorption : ∫ x in Metric.closedBall (0 : R3) R, w x * (η x)^2 * HPDE_01.gradientSq u x ≤
      12 * C₀^2 / (R - r)^2 * ∫ x in Metric.closedBall (0 : R3) R, w x * (u x)^2 := by
    -- Define the cross term: ∑ᵢ (∂ᵢu)(∂ᵢη)
    let cross_term := fun x : R3 => ∑ i : Fin 3, (fderiv ℝ u x) (Pi.single i 1) * (fderiv ℝ η x) (Pi.single i 1)

    -- Define weighted A, B, C functions
    let A_fun := fun x : R3 => w x * (η x)^2 * HPDE_01.gradientSq u x
    let B_fun := fun x : R3 => w x * η x * u x * cross_term x
    let C_fun := fun x : R3 => w x * (u x)^2 * HPDE_01.gradientSq η x

    let S := Metric.closedBall (0 : R3) R

    -- Set up measurability and integrability
    have hS_meas : MeasurableSet S := measurableSet_closedBall
    have hK : IsCompact S := isCompact_closedBall 0 R

    -- Continuity of gradientSq u and gradientSq η
    have h_gradSq_u_cont : Continuous (HPDE_01.gradientSq u) := by
      unfold HPDE_01.gradientSq
      apply continuous_finset_sum
      intro i _
      exact ((hu_smooth.continuous_fderiv (by decide : (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))).clm_apply continuous_const).pow 2

    have h_gradSq_eta_cont : Continuous (HPDE_01.gradientSq η) := by
      unfold HPDE_01.gradientSq
      apply continuous_finset_sum
      intro i _
      exact ((h_smooth.continuous_fderiv (by decide : (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))).clm_apply continuous_const).pow 2

    have h_cross_cont : Continuous cross_term := by
      unfold cross_term
      apply continuous_finset_sum; intro i _
      exact ((hu_smooth.continuous_fderiv (by decide)).clm_apply continuous_const).mul
        ((h_smooth.continuous_fderiv (by decide)).clm_apply continuous_const)

    -- Integrability (all are measurable w times continuous functions, on compact set)
    -- Technical: product of measurable and continuous is integrable on compact
    have hA_int : IntegrableOn A_fun S := by
      -- A = w · η² · gradSq u ≤ w · gradSq u (since η² ≤ 1), dominated by h_w_gradSq_integ
      have h_bound : ∀ᵐ x ∂(volume.restrict (Metric.closedBall (0 : Fin 3 → ℝ) R)),
                     ‖A_fun x‖ ≤ weightedGradientSq w u x := by
        filter_upwards with x
        unfold A_fun weightedGradientSq
        -- 1. Establish non-negativity of all components
        have h_w_nn : 0 ≤ w x := hw_nonneg x
        have h_grad_nn : 0 ≤ HPDE_01.gradientSq u x :=
          Finset.sum_nonneg fun i _ => sq_nonneg _
        -- 2. Establish non-negativity of the product to remove the norm
        have h_prod_nn : 0 ≤ w x * (η x)^2 * HPDE_01.gradientSq u x :=
          mul_nonneg (mul_nonneg h_w_nn (sq_nonneg _)) h_grad_nn
        -- 3. Remove norm from LHS (RHS is already without norm)
        rw [Real.norm_of_nonneg h_prod_nn]
        -- 4. Prove the inequality: w * η² * grad ≤ w * grad using η² ≤ 1
        have h_eta_sq_le : (η x)^2 ≤ 1 := by
          have ⟨_, h_le_one⟩ := h_bounds x
          calc (η x)^2 ≤ 1^2 := sq_le_sq' (by linarith) h_le_one
               _ = 1 := one_pow 2
        calc w x * (η x)^2 * HPDE_01.gradientSq u x
            ≤ w x * 1 * HPDE_01.gradientSq u x := by
              apply mul_le_mul_of_nonneg_right
              exact mul_le_mul_of_nonneg_left h_eta_sq_le h_w_nn
              exact h_grad_nn
          _ = w x * HPDE_01.gradientSq u x := by ring
      -- Use IntegrableOn.mono' with the bound
      have h_meas : AEStronglyMeasurable A_fun (volume.restrict S) := by
        unfold A_fun
        apply AEStronglyMeasurable.mul
        apply AEStronglyMeasurable.mul
        · exact hw_meas.aestronglyMeasurable
        · exact (h_smooth.pow 2).continuous.aestronglyMeasurable
        · exact h_gradSq_u_cont.aestronglyMeasurable
      exact h_w_gradSq_integ.mono' h_meas h_bound
    have hB_int : IntegrableOn B_fun S := by
      -- Strategy: Use Cauchy-Schwarz on cross_term and AM-GM for domination
      -- |B_fun| = w * |η * u * cross| ≤ w * |u| * √(gradSq u) * √(gradSq η)
      --         ≤ (√M_eta/2) * (w*u² + w*gradSq u)  [by AM-GM]

      -- Step 1: Bound gradSq η on compact K
      have h_gradSq_eta_bdd : ∃ M_eta ≥ 0, ∀ x ∈ S, HPDE_01.gradientSq η x ≤ M_eta := by
        have h_bdd := hK.exists_bound_of_continuousOn h_gradSq_eta_cont.continuousOn
        obtain ⟨M, hM⟩ := h_bdd
        use M
        constructor
        · have h0 : (0 : R3) ∈ S := mem_closedBall_self hR.le
          have h_nn : 0 ≤ HPDE_01.gradientSq η 0 := Finset.sum_nonneg fun i _ => sq_nonneg _
          have h_norm_bound := hM 0 h0
          calc 0 ≤ HPDE_01.gradientSq η 0 := h_nn
            _ ≤ ‖HPDE_01.gradientSq η 0‖ := le_abs_self _
            _ ≤ M := h_norm_bound
        · intro x hx
          have h_norm_bound := hM x hx
          calc HPDE_01.gradientSq η x ≤ ‖HPDE_01.gradientSq η x‖ := le_abs_self _
            _ ≤ M := h_norm_bound
      obtain ⟨M_eta, hM_eta_nn, hM_eta⟩ := h_gradSq_eta_bdd

      -- Step 2: Cauchy-Schwarz for cross_term: (∑ aᵢbᵢ)² ≤ (∑ aᵢ²)(∑ bᵢ²)
      have h_cross_sq_bound : ∀ x, (cross_term x)^2 ≤ HPDE_01.gradientSq u x * HPDE_01.gradientSq η x := by
        intro x
        unfold cross_term HPDE_01.gradientSq
        -- Standard Cauchy-Schwarz: Finset.sum_mul_sq_le_sq_mul_sq
        exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun i => (fderiv ℝ u x) (Pi.single i 1))
          (fun i => (fderiv ℝ η x) (Pi.single i 1))

      -- Step 3: AM-GM: |a| * |b| ≤ (a² + b²)/2
      have h_amgm : ∀ a b : ℝ, |a| * |b| ≤ (a^2 + b^2) / 2 := by
        intro a b
        have h := sq_nonneg (|a| - |b|)
        calc |a| * |b| = (|a|^2 + |b|^2 - (|a| - |b|)^2) / 2 := by ring
          _ ≤ (|a|^2 + |b|^2) / 2 := by linarith
          _ = (a^2 + b^2) / 2 := by rw [sq_abs, sq_abs]

      -- Step 4: Domination bound using Cauchy-Schwarz + AM-GM
      -- Technical: |B_fun| ≤ (√M_eta/2) * (w*u² + w*gradSq u) which is integrable
      have h_dom : ∀ᵐ x ∂(volume.restrict S), ‖B_fun x‖ ≤
          (Real.sqrt M_eta / 2) * (w x * (u x)^2 + weightedGradientSq w u x) := by
        filter_upwards with x
        unfold B_fun weightedGradientSq
        have hw_x := hw_nonneg x
        have h_eta_bdd := (h_bounds x).2  -- η x ≤ 1
        have h_eta_nn := (h_bounds x).1   -- 0 ≤ η x

        -- |cross| ≤ √(gradSq u) * √M_eta from CS on S
        have h_cross_abs : |cross_term x| ≤ Real.sqrt (HPDE_01.gradientSq u x) * Real.sqrt M_eta := by
          have h_sq := h_cross_sq_bound x
          have h_grad_u_nn : 0 ≤ HPDE_01.gradientSq u x := Finset.sum_nonneg fun i _ => sq_nonneg _
          have h_grad_eta_nn : 0 ≤ HPDE_01.gradientSq η x := Finset.sum_nonneg fun i _ => sq_nonneg _
          by_cases hx_mem : x ∈ S
          · have h_eta_bound := hM_eta x hx_mem
            calc |cross_term x| = Real.sqrt ((cross_term x)^2) := (Real.sqrt_sq_eq_abs _).symm
              _ ≤ Real.sqrt (HPDE_01.gradientSq u x * HPDE_01.gradientSq η x) :=
                  Real.sqrt_le_sqrt h_sq
              _ = Real.sqrt (HPDE_01.gradientSq u x) * Real.sqrt (HPDE_01.gradientSq η x) :=
                  Real.sqrt_mul h_grad_u_nn _
              _ ≤ Real.sqrt (HPDE_01.gradientSq u x) * Real.sqrt M_eta := by
                  apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h_eta_bound)
                  exact Real.sqrt_nonneg _
          · -- x ∉ S: fderiv η = 0 (η is constant 0 outside B_R)
            -- The key: x ∉ closedBall 0 R, so there's a neighborhood in (closedBall 0 R)ᶜ
            -- which is a subset of (ball 0 R)ᶜ where η = 0
            have h_zero_nhbd : η =ᶠ[nhds x] (fun _ => 0) := by
              have h_open : IsOpen (closedBall (0 : R3) R)ᶜ := isClosed_closedBall.isOpen_compl
              filter_upwards [h_open.mem_nhds hx_mem] with y hy
              exact h_zero y (fun hy_ball => hy (Metric.ball_subset_closedBall hy_ball))
            -- fderiv of locally constant 0 is 0
            have h_fderiv_eta : fderiv ℝ η x = 0 := by
              rw [h_zero_nhbd.fderiv_eq]
              show fderiv ℝ (fun _ : R3 => (0 : ℝ)) x = 0
              rw [show (fun _ : R3 => (0 : ℝ)) = Function.const R3 (0 : ℝ) from rfl]
              exact congrFun (fderiv_const (0 : ℝ)) x
            -- cross_term = 0 since all partials of η are 0
            have h_cross_zero : cross_term x = 0 := by
              unfold cross_term
              simp only [h_fderiv_eta, ContinuousLinearMap.zero_apply, mul_zero,
                Finset.sum_const_zero]
            rw [h_cross_zero, abs_zero]
            exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

        -- Now combine: |B| = w * |η * u * cross| ≤ w * |u| * |cross|
        -- Use: |η| ≤ 1, so w * |η| ≤ w
        -- Then w * |u| * |cross| ≤ w * |u| * √(gradSq u) * √M_eta
        -- By AM-GM: |u| * √(gradSq u) ≤ (u² + gradSq u)/2
        calc ‖w x * η x * u x * cross_term x‖
            = |w x * η x * u x * cross_term x| := Real.norm_eq_abs _
          _ = w x * |η x| * |u x| * |cross_term x| := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hw_x]
          _ ≤ w x * 1 * |u x| * |cross_term x| := by
              apply mul_le_mul_of_nonneg_right
              apply mul_le_mul_of_nonneg_right
              apply mul_le_mul_of_nonneg_left _ hw_x
              rw [abs_of_nonneg h_eta_nn]; exact h_eta_bdd
              exact abs_nonneg _
              exact abs_nonneg _
          _ = w x * |u x| * |cross_term x| := by ring
          _ ≤ w x * |u x| * (Real.sqrt (HPDE_01.gradientSq u x) * Real.sqrt M_eta) := by
              apply mul_le_mul_of_nonneg_left h_cross_abs
              exact mul_nonneg hw_x (abs_nonneg _)
          _ = Real.sqrt M_eta * (w x * |u x| * Real.sqrt (HPDE_01.gradientSq u x)) := by ring
          _ ≤ Real.sqrt M_eta * (w x * (((u x)^2 + HPDE_01.gradientSq u x) / 2)) := by
              apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
              -- Factor out w and use AM-GM
              have h_gradSq_nn : 0 ≤ HPDE_01.gradientSq u x := Finset.sum_nonneg fun i _ => sq_nonneg _
              have h := h_amgm (u x) (Real.sqrt (HPDE_01.gradientSq u x))
              calc w x * |u x| * Real.sqrt (HPDE_01.gradientSq u x)
                  = w x * (|u x| * Real.sqrt (HPDE_01.gradientSq u x)) := by ring
                _ = w x * (|u x| * |Real.sqrt (HPDE_01.gradientSq u x)|) := by
                    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
                _ ≤ w x * (((u x)^2 + (Real.sqrt (HPDE_01.gradientSq u x))^2) / 2) := by
                    apply mul_le_mul_of_nonneg_left h hw_x
                _ = w x * (((u x)^2 + HPDE_01.gradientSq u x) / 2) := by
                    rw [Real.sq_sqrt h_gradSq_nn]
          _ = (Real.sqrt M_eta / 2) * (w x * (u x)^2 + w x * HPDE_01.gradientSq u x) := by ring
          _ = (Real.sqrt M_eta / 2) * (w x * (u x)^2 + weightedGradientSq w u x) := rfl

      -- Step 5: Apply IntegrableOn.mono'
      have h_meas_B : AEStronglyMeasurable B_fun (volume.restrict S) := by
        unfold B_fun
        apply AEStronglyMeasurable.mul
        apply AEStronglyMeasurable.mul
        apply AEStronglyMeasurable.mul
        · exact hw_meas.aestronglyMeasurable
        · exact h_smooth.continuous.aestronglyMeasurable
        · exact hu_smooth.continuous.aestronglyMeasurable
        · exact h_cross_cont.aestronglyMeasurable

      have h_dominator_int : IntegrableOn
          (fun x => (Real.sqrt M_eta / 2) * (w x * (u x)^2 + weightedGradientSq w u x)) S :=
        (h_w_u_integ.add h_w_gradSq_integ).const_mul (Real.sqrt M_eta / 2)

      exact h_dominator_int.mono' h_meas_B h_dom

    have hC_int : IntegrableOn C_fun S := by
      -- C_fun = w * u² * gradSq η ≤ M_eta * w * u² (since gradSq η ≤ M_eta on S)
      -- Get bound on gradSq η
      have h_gradSq_eta_bdd : ∃ M_eta ≥ 0, ∀ x ∈ S, HPDE_01.gradientSq η x ≤ M_eta := by
        have h_bdd := hK.exists_bound_of_continuousOn h_gradSq_eta_cont.continuousOn
        obtain ⟨M, hM⟩ := h_bdd
        use M
        constructor
        · have h0 : (0 : R3) ∈ S := mem_closedBall_self hR.le
          have h_norm_bound := hM 0 h0
          have h_nn : 0 ≤ HPDE_01.gradientSq η 0 := Finset.sum_nonneg fun i _ => sq_nonneg _
          calc 0 ≤ HPDE_01.gradientSq η 0 := h_nn
            _ ≤ ‖HPDE_01.gradientSq η 0‖ := le_abs_self _
            _ ≤ M := h_norm_bound
        · intro x hx
          have h_norm_bound := hM x hx
          calc HPDE_01.gradientSq η x ≤ ‖HPDE_01.gradientSq η x‖ := le_abs_self _
            _ ≤ M := h_norm_bound
      obtain ⟨M_eta, hM_eta_nn, hM_eta⟩ := h_gradSq_eta_bdd

      -- Domination bound
      have h_dom : ∀ᵐ x ∂(volume.restrict S), ‖C_fun x‖ ≤ M_eta * (w x * (u x)^2) := by
        filter_upwards [ae_restrict_mem hS_meas] with x hx_mem
        unfold C_fun
        have hw_x := hw_nonneg x
        have h_grad_eta_bound := hM_eta x hx_mem
        have h_grad_nn : 0 ≤ HPDE_01.gradientSq η x := Finset.sum_nonneg fun i _ => sq_nonneg _
        have h_prod_nn : 0 ≤ w x * (u x)^2 * HPDE_01.gradientSq η x :=
          mul_nonneg (mul_nonneg hw_x (sq_nonneg _)) h_grad_nn
        rw [Real.norm_of_nonneg h_prod_nn]
        calc w x * (u x)^2 * HPDE_01.gradientSq η x
            ≤ w x * (u x)^2 * M_eta := by
              apply mul_le_mul_of_nonneg_left h_grad_eta_bound
              exact mul_nonneg hw_x (sq_nonneg _)
          _ = M_eta * (w x * (u x)^2) := by ring

      -- Measurability and integrability
      have h_meas_C : AEStronglyMeasurable C_fun (volume.restrict S) := by
        unfold C_fun
        apply AEStronglyMeasurable.mul
        apply AEStronglyMeasurable.mul
        · exact hw_meas.aestronglyMeasurable
        · exact (hu_smooth.pow 2).continuous.aestronglyMeasurable
        · exact h_gradSq_eta_cont.aestronglyMeasurable

      have h_dominator_int : IntegrableOn (fun x => M_eta * (w x * (u x)^2)) S :=
        h_w_u_integ.const_mul M_eta

      exact h_dominator_int.mono' h_meas_C h_dom

    -- Nonnegativity of A and C
    have hA_nonneg : ∀ x ∈ S, 0 ≤ A_fun x := fun x _ => by
      apply mul_nonneg
      apply mul_nonneg (hw_nonneg x) (sq_nonneg _)
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
    have hC_nonneg : ∀ x ∈ S, 0 ≤ C_fun x := fun x _ => by
      apply mul_nonneg
      apply mul_nonneg (hw_nonneg x) (sq_nonneg _)
      exact Finset.sum_nonneg fun i _ => sq_nonneg _

    -- Step 4: Derive integral identity from weak harmonicity
    -- Expand: ∂ᵢ(η²u) = 2ηu·∂ᵢη + η²·∂ᵢu
    -- So: ∫ w · ∑ᵢ (∂ᵢu)(2ηu·∂ᵢη + η²·∂ᵢu) = 0
    -- = ∫ w·η²·gradSq u + 2·∫ w·ηu·cross_term = 0
    -- This gives: (∫ A) + 2*(∫ B) = 0

    have h_integral_identity : (∫ x in S, A_fun x) + 2 * (∫ x in S, B_fun x) = 0 := by
      -- Use h_weak and expand the fderiv of φ = η²u
      -- φ = η² * u, so fderiv φ = 2η·u·fderiv η + η²·fderiv u (by product rule)
      -- Expanding: ∑ᵢ (∂ᵢu)(∂ᵢφ) = ∑ᵢ (∂ᵢu)(2ηu·∂ᵢη + η²·∂ᵢu)
      --                         = η²·gradSq u + 2·η·u·cross_term
      -- Technical proof of fderiv expansion deferred to later cleanup
      have h_expand : ∀ x, ∑ i : Fin 3, (fderiv ℝ u x) (Pi.single i 1) * (fderiv ℝ φ x) (Pi.single i 1) =
          (η x)^2 * HPDE_01.gradientSq u x + 2 * (η x * u x * cross_term x) := fun x => by
        -- Use HPDE_01.gradient_inner_product_expansion and reorder
        have hη_diff : DifferentiableAt ℝ η x := h_smooth.differentiable (by decide : (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)) |>.differentiableAt
        have hu_diff : DifferentiableAt ℝ u x := hu_smooth.differentiable (by decide : (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)) |>.differentiableAt
        have h_gi := HPDE_01.gradient_inner_product_expansion η u x hη_diff hu_diff
        -- h_gi : ∑ i, ∂ᵢu * ∂ᵢ(η²u) = 2ηu·cross + η²·gradSq u
        -- Goal: ∑ i, ∂ᵢu * ∂ᵢφ = η²·gradSq u + 2·(ηu·cross)
        -- Note φ = fun y => (η y)^2 * u y, so fderiv φ = fderiv (fun y => (η y)^2 * u y)
        calc ∑ i : Fin 3, (fderiv ℝ u x) (Pi.single i 1) * (fderiv ℝ φ x) (Pi.single i 1)
            = 2 * η x * u x * ∑ i : Fin 3, (fderiv ℝ u x) (Pi.single i 1) * (fderiv ℝ η x) (Pi.single i 1) +
              (η x)^2 * ∑ i : Fin 3, ((fderiv ℝ u x) (Pi.single i 1))^2 := h_gi
          _ = 2 * η x * u x * cross_term x + (η x)^2 * HPDE_01.gradientSq u x := rfl
          _ = (η x)^2 * HPDE_01.gradientSq u x + 2 * (η x * u x * cross_term x) := by ring
      -- Now use h_weak: ∫ w · (sum of ∂u·∂φ) = 0
      have h_weak_rewrite : ∫ x in S, w x * ((η x)^2 * HPDE_01.gradientSq u x + 2 * (η x * u x * cross_term x)) = 0 := by
        calc ∫ x in S, w x * ((η x)^2 * HPDE_01.gradientSq u x + 2 * (η x * u x * cross_term x))
            = ∫ x in S, w x * ∑ i : Fin 3, (fderiv ℝ u x) (Pi.single i 1) * (fderiv ℝ φ x) (Pi.single i 1) := by
              congr 1; ext x; rw [← h_expand x]
          _ = 0 := h_weak
      -- Split the integral
      have h_split : ∫ x in S, w x * ((η x)^2 * HPDE_01.gradientSq u x + 2 * (η x * u x * cross_term x)) =
          (∫ x in S, A_fun x) + 2 * (∫ x in S, B_fun x) := by
        have h_eq : ∀ x, w x * ((η x)^2 * HPDE_01.gradientSq u x + 2 * (η x * u x * cross_term x)) =
            A_fun x + 2 * B_fun x := fun x => by
          unfold A_fun B_fun
          ring
        rw [show (fun x => w x * ((η x)^2 * HPDE_01.gradientSq u x + 2 * (η x * u x * cross_term x))) =
            (fun x => A_fun x + 2 * B_fun x) from funext h_eq]
        rw [integral_add hA_int (hB_int.const_mul 2)]
        simp only [← smul_eq_mul, integral_smul]
      rw [← h_split, h_weak_rewrite]

    -- Step 5: Pointwise Young's inequality bound
    -- |2·B(x)| ≤ (1/2)·A(x) + 2·C(x)
    have h_pt : ∀ x ∈ S, |2 * B_fun x| ≤ (1/2) * A_fun x + 2 * C_fun x := by
      intro x _
      unfold A_fun B_fun C_fun
      have hw_x := hw_nonneg x
      -- Use coordwise_young_for_gradient_half from HPDE-01
      have h_young := HPDE_01.coordwise_young_for_gradient_half (η x) (u x)
        (fun i => (fderiv ℝ u x) (Pi.single i 1))
        (fun i => (fderiv ℝ η x) (Pi.single i 1))
      -- h_young states: |2 * η * u * ∑ᵢ (∂ᵢu)(∂ᵢη)| ≤ (1/2)*η²*∑(∂ᵢu)² + 2*u²*∑(∂ᵢη)²
      -- We need: |2 * w * η * u * cross| ≤ (1/2)*w*η²*gradSq u + 2*w*u²*gradSq η
      -- Factor out w ≥ 0 and use h_young
      calc |2 * (w x * η x * u x * cross_term x)|
          = w x * |2 * η x * u x * cross_term x| := by
            rw [show 2 * (w x * η x * u x * cross_term x) = w x * (2 * η x * u x * cross_term x) by ring]
            rw [abs_mul, abs_of_nonneg hw_x]
        _ ≤ w x * ((1/2) * (η x)^2 * HPDE_01.gradientSq u x + 2 * (u x)^2 * HPDE_01.gradientSq η x) := by
            apply mul_le_mul_of_nonneg_left _ hw_x
            -- Technical conversion: match cross_term with sum and gradientSq with sum
            -- The algebraic identity holds by definition
            have h_cross_eq : cross_term x = ∑ i : Fin 3, (fderiv ℝ u x) (Pi.single i 1) * (fderiv ℝ η x) (Pi.single i 1) := rfl
            have h_gradSq_u_eq : HPDE_01.gradientSq u x = ∑ i : Fin 3, ((fderiv ℝ u x) (Pi.single i 1))^2 := rfl
            have h_gradSq_eta_eq : HPDE_01.gradientSq η x = ∑ i : Fin 3, ((fderiv ℝ η x) (Pi.single i 1))^2 := rfl
            rw [h_cross_eq, h_gradSq_u_eq, h_gradSq_eta_eq]
            convert h_young using 2
        _ = (1/2) * (w x * (η x)^2 * HPDE_01.gradientSq u x) + 2 * (w x * (u x)^2 * HPDE_01.gradientSq η x) := by ring

    -- Step 6: Apply absorption_from_cross_bound
    have h_absorb : ∫ x in S, A_fun x ≤ 4 * ∫ x in S, C_fun x :=
      HPDE_01.absorption_from_cross_bound hS_meas hA_int hB_int hC_int hA_nonneg hC_nonneg
        h_integral_identity h_pt

    -- Step 7: Chain with gradient bound
    -- gradSq η ≤ 3 · ‖fderiv η‖² ≤ 3 · C₀²/(R-r)²
    have h_grad_sq_bound : ∀ x, HPDE_01.gradientSq η x ≤ 3 * C₀^2 / (R - r)^2 := by
      intro x
      have h1 := h_grad_bound x  -- ‖fderiv ℝ η x‖ ≤ C₀ / (R - r)
      have h2 := HPDE_01.gradientSq_le_three_mul_fderiv_norm_sq η x
      calc HPDE_01.gradientSq η x
          ≤ 3 * ‖fderiv ℝ η x‖^2 := h2
        _ ≤ 3 * (C₀ / (R - r))^2 := by
            apply mul_le_mul_of_nonneg_left
            · exact sq_le_sq' (by linarith [h1, norm_nonneg (fderiv ℝ η x)]) h1
            · norm_num
        _ = 3 * C₀^2 / (R - r)^2 := by
            have h_pos : 0 < R - r := sub_pos.mpr hrR
            field_simp

    -- Bound ∫C in terms of ∫w·u²
    have h_C_bound : ∫ x in S, C_fun x ≤ 3 * C₀^2 / (R - r)^2 * ∫ x in S, w x * (u x)^2 := by
      have h_pt_C : ∀ x, C_fun x ≤ 3 * C₀^2 / (R - r)^2 * (w x * (u x)^2) := fun x => by
        unfold C_fun
        calc w x * (u x)^2 * HPDE_01.gradientSq η x
            ≤ w x * (u x)^2 * (3 * C₀^2 / (R - r)^2) := by
              apply mul_le_mul_of_nonneg_left (h_grad_sq_bound x)
              exact mul_nonneg (hw_nonneg x) (sq_nonneg _)
          _ = 3 * C₀^2 / (R - r)^2 * (w x * (u x)^2) := by ring
      have h_wu2_int : IntegrableOn (fun x => w x * (u x)^2) S := h_w_u_integ
      calc ∫ x in S, C_fun x
          ≤ ∫ x in S, 3 * C₀^2 / (R - r)^2 * (w x * (u x)^2) :=
            setIntegral_mono_on hC_int (h_wu2_int.const_mul _) hS_meas (fun x _ => h_pt_C x)
        _ = 3 * C₀^2 / (R - r)^2 * ∫ x in S, w x * (u x)^2 := by
            simp only [← smul_eq_mul]; exact integral_smul _ _

    -- Final chain: ∫A ≤ 4∫C ≤ 12·C₀²/(R-r)² · ∫w·u²
    calc ∫ x in S, A_fun x
        ≤ 4 * ∫ x in S, C_fun x := h_absorb
      _ ≤ 4 * (3 * C₀^2 / (R - r)^2 * ∫ x in S, w x * (u x)^2) :=
          mul_le_mul_of_nonneg_left h_C_bound (by norm_num : (4 : ℝ) ≥ 0)
      _ = 12 * C₀^2 / (R - r)^2 * ∫ x in S, w x * (u x)^2 := by ring

  -- Step 8: Inner ball restriction (η = 1 on B_r)
  have h_inner_ball : ∫ x in Metric.closedBall (0 : R3) r, weightedGradientSq w u x ≤
      ∫ x in Metric.closedBall (0 : R3) R, w x * (η x)^2 * HPDE_01.gradientSq u x := by
    -- Since η = 1 on B_r: weightedGradientSq w u = w · gradientSq u = w · η² · gradientSq u
    have h_eq : ∀ x ∈ Metric.closedBall (0 : R3) r,
        weightedGradientSq w u x = w x * (η x)^2 * HPDE_01.gradientSq u x := fun x hx => by
      unfold weightedGradientSq
      rw [h_one x hx, one_pow, mul_one]
    -- Rewrite LHS using equality on B_r
    have h_int_eq : ∫ x in Metric.closedBall (0 : R3) r, weightedGradientSq w u x =
        ∫ x in Metric.closedBall (0 : R3) r, w x * (η x)^2 * HPDE_01.gradientSq u x :=
      setIntegral_congr_fun measurableSet_closedBall h_eq
    rw [h_int_eq]
    -- Use monotonicity: B_r ⊆ B_R and integrand is nonneg
    have h_nonneg : ∀ x, 0 ≤ w x * (η x)^2 * HPDE_01.gradientSq u x := fun x => by
      apply mul_nonneg
      apply mul_nonneg (hw_nonneg x) (sq_nonneg _)
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
    have h_subset : Metric.closedBall (0 : R3) r ⊆ Metric.closedBall (0 : R3) R :=
      Metric.closedBall_subset_closedBall (le_of_lt hrR)
    -- Need integrability on larger ball
    have h_integrable : IntegrableOn (fun x => w x * (η x)^2 * HPDE_01.gradientSq u x)
        (Metric.closedBall (0 : R3) R) := by
      -- Key insight: w · η² · gradSq ≤ w · gradSq = weightedGradientSq w u
      -- since η ∈ [0,1], so η² ≤ 1
      -- We dominate by h_w_gradSq_integ using Integrable.mono
      have h_eta_sq_le : ∀ x, (η x)^2 ≤ 1 := fun x => by
        have ⟨h_nn, h_le⟩ := h_bounds x
        calc (η x)^2 ≤ 1^2 := sq_le_sq' (by linarith) h_le
           _ = 1 := one_pow 2
      -- Pointwise bound: w · η² · gradSq ≤ w · gradSq
      have h_pt_bound : ∀ x, w x * (η x)^2 * HPDE_01.gradientSq u x ≤
          w x * HPDE_01.gradientSq u x := fun x => by
        apply mul_le_mul_of_nonneg_right
        · calc w x * (η x)^2 ≤ w x * 1 :=
              mul_le_mul_of_nonneg_left (h_eta_sq_le x) (hw_nonneg x)
            _ = w x := mul_one _
        · exact Finset.sum_nonneg fun i _ => sq_nonneg _
      -- The RHS equals weightedGradientSq w u
      have h_eq_wGradSq : ∀ x, w x * HPDE_01.gradientSq u x = weightedGradientSq w u x :=
        fun _ => rfl
      -- Apply IntegrableOn.mono: f ≤ g pointwise, g integrable ⟹ f integrable
      -- First show the integrand is nonneg (so |f| = f)
      have h_integrand_nonneg : ∀ x, 0 ≤ w x * (η x)^2 * HPDE_01.gradientSq u x := fun x => by
        apply mul_nonneg
        apply mul_nonneg (hw_nonneg x) (sq_nonneg _)
        exact Finset.sum_nonneg fun i _ => sq_nonneg _
      have h_dom_nonneg : ∀ x, 0 ≤ weightedGradientSq w u x := fun x => by
        unfold weightedGradientSq
        exact mul_nonneg (hw_nonneg x) (Finset.sum_nonneg fun i _ => sq_nonneg _)
      -- Use mono: 0 ≤ f ≤ g, g integrable ⟹ f integrable
      -- First, establish continuity of gradientSq u
      have h_gradSq_cont : Continuous (HPDE_01.gradientSq u) := by
        unfold HPDE_01.gradientSq
        apply continuous_finset_sum
        intro i _
        have h_cont : Continuous (fun x => (fderiv ℝ u x) (Pi.single i 1)) :=
          (hu_smooth.continuous_fderiv (by decide : (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))).clm_apply continuous_const
        exact h_cont.pow 2
      refine h_w_gradSq_integ.mono' ?_ (ae_of_all _ fun x => ?_)
      · -- AEStronglyMeasurable: f is meas since w, η², gradSq are continuous/measurable
        apply AEStronglyMeasurable.mul
        apply AEStronglyMeasurable.mul
        · exact hw_meas.aestronglyMeasurable
        · exact (h_smooth.pow 2).continuous.aestronglyMeasurable
        · exact h_gradSq_cont.aestronglyMeasurable
      · -- Pointwise bound: f ≤ g
        rw [Real.norm_of_nonneg (h_integrand_nonneg x)]
        calc w x * (η x)^2 * HPDE_01.gradientSq u x
            ≤ w x * HPDE_01.gradientSq u x := h_pt_bound x
          _ = weightedGradientSq w u x := (h_eq_wGradSq x).symm
    exact setIntegral_mono_set h_integrable (ae_of_all _ h_nonneg) (ae_of_all _ h_subset)

  -- Combine and conclude
  use 12 * C₀^2
  constructor
  · -- 12 * C₀² > 0
    exact mul_pos (by norm_num : (12 : ℝ) > 0) (sq_pos_of_pos hC₀_pos)
  · -- Chain the estimates
    calc ∫ x in Metric.closedBall (0 : R3) r, weightedGradientSq w u x
        ≤ ∫ x in Metric.closedBall (0 : R3) R, w x * (η x)^2 * HPDE_01.gradientSq u x := h_inner_ball
      _ ≤ 12 * C₀^2 / (R - r)^2 * ∫ x in Metric.closedBall (0 : R3) R, w x * (u x)^2 := h_absorption

/--
Specialized weighted Caccioppoli for power weights |x|^α where -3 < α < 3.

For power weights, we have explicit integrability conditions from the
dimension constraint: the weight is integrable near 0 when α > -3.
-/
theorem power_weighted_caccioppoli (u : R3 → ℝ) (α : ℝ) (R r : ℝ)
    (hR : 0 < R) (hr : 0 < r) (hrR : r < R)
    (hα : -3 < α ∧ α < 3)
    (hu_smooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (h_harmonic : IsWeightedHarmonicOn u (powerWeight α) R)
    (h_w_u_integ : IntegrableOn (fun x => powerWeight α x * (u x)^2) (Metric.closedBall 0 R) volume)
    (h_w_gradSq_integ : IntegrableOn (fun x => weightedGradientSq (powerWeight α) u x) (Metric.closedBall 0 R) volume) :
    ∃ C > 0, ∫ x in Metric.closedBall (0 : R3) r, weightedGradientSq (powerWeight α) u x ≤
      C / (R - r)^2 * ∫ x in Metric.closedBall (0 : R3) R, powerWeight α x * (u x)^2 := by
  -- This follows from weighted_caccioppoli + powerWeight properties
  have hw_nonneg : ∀ x, 0 ≤ powerWeight α x := fun x => Real.rpow_nonneg (norm_nonneg x) α
  have hw_meas : Measurable (powerWeight α) := by
    unfold powerWeight
    -- powerWeight α x = ‖x‖^α is measurable for all α ∈ ℝ
    -- Key: Real.hasMeasurablePow gives MeasurablePow ℝ ℝ instance
    -- So Measurable.pow_const applies: measurable_norm.pow_const α
    exact measurable_norm.pow_const α
  exact weighted_caccioppoli u (powerWeight α) R r hR hr hrR hu_smooth hw_nonneg hw_meas
    h_harmonic h_w_u_integ h_w_gradSq_integ

end HPDE_02
