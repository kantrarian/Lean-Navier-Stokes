import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import HPDE_common.CylinderNotation

open Metric Filter

namespace HPDE_common

/-!
# Smooth Cutoff Functions for Caccioppoli

This file provides the existence of smooth cutoff functions adapted to
concentric balls, with controlled gradient bounds.

## Main Results

1. `exists_smooth_cutoff_ball_basic`: Basic smooth cutoff without gradient bound
   - **This is the first DeepSeek Prover v2 target**
   - η smooth, η = 1 on B_r, η = 0 outside B_R

2. `exists_smooth_cutoff_ball`: Full version with quantitative gradient bound
   - Adds: ‖∇η‖ ≤ C/(R-r) for universal constant C

## Strategy for DeepSeek (Basic Version)

1. Use a 1D smooth bump φ on ℝ with φ ≡ 1 on [0, r] and φ ≡ 0 on [R, ∞)
2. Define η(x) := φ(‖x‖)
3. Use `ContDiff.comp` and properties of `norm` to get smoothness
4. Check the support / plateau conditions

## Strategy for Full Version (Gradient Bound)

1. Start from the basic version
2. Use chain rule: ∇η(x) = φ'(‖x‖) · x/‖x‖ for x ≠ 0
3. Estimate |φ'| after scaling [r,R] to a standard interval
4. Conclude universal C/(R-r) bound
-/

/--
A smooth cutoff adapted to two concentric balls in `R3`.

Note: We use `(⊤ : ℕ∞)` in the smoothness type rather than just `⊤` because:
- `⊤ : WithTop ℕ∞` means analytic (which bump functions are NOT - they have compact support)
- `(⊤ : ℕ∞)` coerced to `WithTop ℕ∞` means C^∞ smooth (which bump functions ARE)

For PDE applications (Caccioppoli, energy estimates, etc.), C^∞ is exactly what we need.
-/
lemma exists_smooth_cutoff_ball_basic
    (r R : ℝ) (hr : 0 < r) (hR : r < R) :
    ∃ (η : R3 → ℝ),
      (ContDiff ℝ (⊤ : ℕ∞) η) ∧
      (∀ x : R3, x ∈ closedBall (0 : R3) r → η x = 1) ∧
      (∀ x : R3, x ∉ ball (0 : R3) R → η x = 0) := by
  -- Construct the bump function from Mathlib
  let f : ContDiffBump (0 : R3) := ⟨r, R, hr, hR⟩
  use f
  constructor
  · -- Smoothness: ContDiff ℝ (⊤ : ℕ∞) f
    exact f.contDiff

  constructor
  · -- Plateau: ∀ x ∈ closedBall 0 r, f x = 1
    intro x hx
    exact f.one_of_mem_closedBall hx

  · -- Support: ∀ x ∉ ball 0 R, f x = 0
    intro x hx
    apply f.zero_of_le_dist
    exact not_lt.mp (mem_ball.not.mp hx)

/--
A smooth cutoff with quantitative gradient bound.

This extends `exists_smooth_cutoff_ball_basic` with a gradient estimate,
which is the key ingredient for Caccioppoli inequalities.
-/
lemma exists_smooth_cutoff_ball
    (r R : ℝ) (hr : 0 < r) (hR : r < R) :
    ∃ (η : R3 → ℝ),
      (ContDiff ℝ (⊤ : ℕ∞) η) ∧
      (∀ x : R3, x ∈ closedBall (0 : R3) r → η x = 1) ∧
      (∀ x : R3, x ∉ ball (0 : R3) R → η x = 0) ∧
      (∀ x : R3, 0 ≤ η x ∧ η x ≤ 1) ∧
      (∃ C > 0, ∀ x : R3, ‖fderiv ℝ η x‖ ≤ C / (R - r)) := by
  -- Construct the bump function from Mathlib
  let f : ContDiffBump (0 : R3) := ⟨r, R, hr, hR⟩
  use f
  refine ⟨?_, ?_, ?_, ?_, ?_⟩

  -- 1. Smoothness
  · exact f.contDiff

  -- 2. Plateau: η = 1 on B_r
  · intro x hx
    exact f.one_of_mem_closedBall hx

  -- 3. Support: η = 0 outside B_R
  · intro x hx
    apply f.zero_of_le_dist
    exact not_lt.mp (mem_ball.not.mp hx)

  -- 4. Bounds: 0 ≤ η ≤ 1
  · intro x
    exact ⟨f.nonneg, f.le_one⟩

  -- 5. Gradient bound: ∃ C > 0, ‖∇η‖ ≤ C/(R-r)
  -- Strategy: smooth functions on compact sets have bounded derivatives.
  -- We show ∃ C_abs bounding ‖∇η‖, then C = C_abs * (R-r) gives C/(R-r) = C_abs.
  · -- Step 5a: fderiv f is continuous (since f is smooth)
    have h_smooth : ContDiff ℝ (⊤ : ℕ∞) (f : R3 → ℝ) := f.contDiff
    have h_one_le : (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) := by decide
    have h_cont_fderiv : Continuous (fderiv ℝ (f : R3 → ℝ)) :=
      h_smooth.continuous_fderiv h_one_le
    -- Step 5b: closedBall is compact in finite dimensions
    have h_compact : IsCompact (closedBall (0 : R3) R) := isCompact_closedBall 0 R
    -- Step 5c: fderiv itself is continuous (not its norm), then we get the bound
    -- We use exists_bound_of_continuousOn on the fderiv function
    have h_cont_on_fderiv : ContinuousOn (fderiv ℝ (f : R3 → ℝ)) (closedBall 0 R) :=
      h_cont_fderiv.continuousOn
    -- Get bound on the operator norm of fderiv
    obtain ⟨C_abs, hC_abs⟩ := h_compact.exists_bound_of_continuousOn h_cont_on_fderiv
    -- Step 5d: Construct C = C_abs * (R - r) + 1 to ensure C > 0
    use C_abs * (R - r) + 1
    constructor
    · -- C > 0
      have h_pos : 0 < R - r := sub_pos.mpr hR
      have h_nonneg : 0 ≤ C_abs * (R - r) := by
        apply mul_nonneg _ h_pos.le
        -- C_abs ≥ 0 since it bounds a norm
        by_contra h_neg
        push_neg at h_neg
        -- 0 ∈ closedBall 0 R
        have h0 : (0 : R3) ∈ closedBall (0 : R3) R := mem_closedBall_self (lt_trans hr hR).le
        have := hC_abs 0 h0
        linarith [norm_nonneg (fderiv ℝ (f : R3 → ℝ) 0)]
      linarith
    · -- ∀ x, ‖∇η x‖ ≤ C / (R - r)
      intro x
      by_cases hx : x ∈ closedBall (0 : R3) R
      · -- Inside ball: use the bound
        have h_bound := hC_abs x hx
        have h_pos : 0 < R - r := sub_pos.mpr hR
        calc ‖fderiv ℝ (f : R3 → ℝ) x‖
            ≤ C_abs := h_bound
          _ ≤ C_abs + 1 / (R - r) := le_add_of_nonneg_right (div_nonneg zero_le_one h_pos.le)
          _ ≤ (C_abs * (R - r) + 1) / (R - r) := by field_simp; ring_nf; nlinarith
      · -- Outside ball: f is identically 0 in a neighborhood, so fderiv = 0
        have h_pos : 0 < R - r := sub_pos.mpr hR
        -- x is strictly outside closedBall 0 R, so dist x 0 > R
        have h_dist : R < dist x 0 := not_le.mp (mem_closedBall.not.mp hx)
        -- The set {y | R < dist y 0} is open and contains x
        have h_open : IsOpen {y : R3 | R < dist y 0} :=
          isOpen_lt continuous_const (continuous_id.dist continuous_const)
        -- f ≡ 0 in a neighborhood of x (since f = 0 outside ball 0 R)
        have h_zero_nbhd : (f : R3 → ℝ) =ᶠ[nhds x] (fun _ => 0) := by
          filter_upwards [h_open.mem_nhds h_dist] with y hy
          apply f.zero_of_le_dist
          linarith
        -- fderiv of locally constant function = fderiv of constant = 0
        have h_fderiv_zero : fderiv ℝ (f : R3 → ℝ) x = 0 := by
          rw [h_zero_nbhd.fderiv_eq]
          show fderiv ℝ (fun _ : R3 => (0 : ℝ)) x = 0
          rw [show (fun _ : R3 => (0 : ℝ)) = Function.const R3 (0 : ℝ) from rfl]
          exact congrFun (fderiv_const (0 : ℝ)) x
        -- ‖0‖ = 0 ≤ positive number
        rw [h_fderiv_zero, norm_zero]
        apply div_nonneg _ h_pos.le
        have h_C_nonneg : 0 ≤ C_abs := by
          by_contra h_neg
          push_neg at h_neg
          have h0 : (0 : R3) ∈ closedBall (0 : R3) R := mem_closedBall_self (lt_trans hr hR).le
          linarith [hC_abs 0 h0, norm_nonneg (fderiv ℝ (f : R3 → ℝ) 0)]
        linarith [mul_nonneg h_C_nonneg h_pos.le]

end HPDE_common
