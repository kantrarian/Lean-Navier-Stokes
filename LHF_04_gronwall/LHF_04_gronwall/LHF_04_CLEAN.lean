import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic

/-!
# LHF-04: Gronwall Inequality - CLEAN VERSION (NO ADMITS, NO HELPER AXIOMS)

Patched 2026-05-23: the three helper axioms previously declared in this file
(`monotonicity_axiom`, `exp_half_lt_two_clean`, `deriv_F_axiom`) have been
discharged to mathlib-only proofs via the AlphaProof-Nexus-style Ralph-loop
pilot. They are kept under their original names (now `theorem` instead of
`axiom`) so downstream call sites are unchanged.

## The Issue
The original version extended hypotheses from `[t₀, t₀+c₁/k]` to `[t₀, ∞)` using `admit`.
This was technical overkill since we only need the bound on the closed interval.

## The Solution
Use a simpler assumption: energy is globally nonnegative and the differential
inequality holds globally. This is physically reasonable (energy is always ≥ 0)
and mathematically cleaner.

## Status: ZERO ADMITS, ZERO AXIOMS - FULLY PROVED
-/

open Real Set Filter Topology

-- Time and parameters
variable (t t₀ τ : ℝ)
variable (k C ε c₁ : ℝ)
variable (hk : k > 0) (hC : C > 0) (hε : ε > 0)

-- Energy functional
variable (E : ℝ → ℝ)

/-!
## Helper Lemmas (formerly axioms; now proved against mathlib)
-/

/-- Monotonicity from non-positive derivative.
    Proved via `antitoneOn_of_deriv_nonpos` on `Set.Icc a b`. -/
theorem monotonicity_axiom {f : ℝ → ℝ} {a b : ℝ} (h_le : a ≤ b)
    (h_diff : DifferentiableOn ℝ f (Set.Ici a))
    (h_deriv_nonpos : ∀ x ∈ Set.Ioo a b, deriv f x ≤ 0) :
    f b ≤ f a := by
  have hsub : Set.Icc a b ⊆ Set.Ici a := Set.Icc_subset_Ici_self
  have hcont : ContinuousOn f (Set.Icc a b) := (h_diff.mono hsub).continuousOn
  have hdiff' : DifferentiableOn ℝ f (interior (Set.Icc a b)) := by
    rw [interior_Icc]
    exact h_diff.mono (Set.Ioo_subset_Icc_self.trans hsub)
  have hderiv : ∀ x ∈ interior (Set.Icc a b), deriv f x ≤ 0 := by
    rw [interior_Icc]
    exact h_deriv_nonpos
  have hanti : AntitoneOn f (Set.Icc a b) :=
    antitoneOn_of_deriv_nonpos (convex_Icc a b) hcont hdiff' hderiv
  exact hanti (Set.left_mem_Icc.mpr h_le) (Set.right_mem_Icc.mpr h_le) h_le

/-- `exp(1/2) < 2`. Proved via `Real.exp_bound'` (Taylor remainder at n=3). -/
theorem exp_half_lt_two_clean : exp (1/2) < 2 := by
  have h := Real.exp_bound' (x := 1/2) (by norm_num) (by norm_num) (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  linarith

/-- Derivative of `F(x) = E(x) * exp(-C·k·x)` via product + chain rule. -/
theorem deriv_F_axiom (F E : ℝ → ℝ) (C k : ℝ) (s : ℝ)
    (hF : F = fun x => E x * exp (-C * k * x))
    (h_diff_at_E : DifferentiableAt ℝ E s) :
    deriv F s = (deriv E s - C * k * E s) * exp (-C * k * s) := by
  subst hF
  have hg : HasDerivAt (fun x : ℝ => -C * k * x) (-C * k) s := by
    simpa using (hasDerivAt_id s).const_mul (-C * k)
  have hexp : HasDerivAt (fun x : ℝ => exp (-C * k * x)) (exp (-C * k * s) * (-C * k)) s :=
    hg.exp
  have hprod : HasDerivAt (fun x : ℝ => E x * exp (-C * k * x))
      (deriv E s * exp (-C * k * s) + E s * (exp (-C * k * s) * (-C * k))) s :=
    h_diff_at_E.hasDerivAt.mul hexp
  rw [hprod.deriv]
  ring

/-!
## Gronwall Exponential Bound (Cleaner Version)

Same as before, but now with the expectation that hypotheses hold globally.
This is physically reasonable: energy is always nonnegative.
-/

theorem gronwall_exponential_bound
  {E : ℝ → ℝ} {C k ε t₀ : ℝ}
  (_hC : C > 0) (_hk : k > 0) (_hε : ε > 0)
  (h_diff : DifferentiableOn ℝ E (Set.Ici t₀))
  (_h_nonneg : ∀ t ≥ t₀, E t ≥ 0)
  (h_deriv : ∀ t ≥ t₀, deriv E t ≤ C * k * E t)
  (h_init : E t₀ ≤ ε) :
  ∀ t ≥ t₀, E t ≤ ε * exp (C * k * (t - t₀)) := by

  intro t ht
  let F := fun s => E s * exp (- C * k * s)

  have hF_diff : DifferentiableOn ℝ F (Set.Ici t₀) := by
    apply DifferentiableOn.mul h_diff
    apply Differentiable.differentiableOn
    apply Differentiable.comp (Differentiable.exp differentiable_id)
    apply Differentiable.const_mul differentiable_id

  have hF_decreasing : ∀ s ∈ Set.Ioo t₀ t, deriv F s ≤ 0 := by
    intro s hs
    -- Correct neighborhood construction
    have h_nhds : Set.Ici t₀ ∈ 𝓝 s := Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioi hs.1) Ioi_subset_Ici_self
    have h_diff_at_E : DifferentiableAt ℝ E s := h_diff.differentiableAt h_nhds
    have _h_deriv_bound : deriv E s ≤ C * k * E s := h_deriv s (le_of_lt hs.1)

    have h_deriv_F : deriv F s = (deriv E s - C * k * E s) * exp (- C * k * s) := by
      apply deriv_F_axiom F E C k s rfl h_diff_at_E

    rw [h_deriv_F]
    have h_exp_pos : 0 < exp (-C * k * s) := exp_pos _
    nlinarith

  have hF_mono : F t ≤ F t₀ := by
    apply monotonicity_axiom ht hF_diff
    intro x hx
    exact hF_decreasing x hx

  -- Algebraic rearrangement
  have h_bound : E t * exp (-C * k * t) ≤ ε * exp (-C * k * t₀) := by
    have h_init' : E t₀ * exp (-C * k * t₀) ≤ ε * exp (-C * k * t₀) :=
      mul_le_mul_of_nonneg_right h_init (le_of_lt (exp_pos _))
    exact le_trans hF_mono h_init'

  -- Multiply by exp(C k t)
  have h_mul : (E t * exp (-C * k * t)) * exp (C * k * t) ≤ (ε * exp (-C * k * t₀)) * exp (C * k * t) :=
    mul_le_mul_of_nonneg_right h_bound (le_of_lt (exp_pos _))

  -- Simplify LHS
  rw [mul_assoc, ← Real.exp_add] at h_mul
  have h_lhs_exp : -C * k * t + C * k * t = 0 := by ring
  rw [h_lhs_exp, Real.exp_zero, mul_one] at h_mul

  -- Simplify RHS
  rw [mul_assoc, ← Real.exp_add] at h_mul
  have h_rhs_exp : -C * k * t₀ + C * k * t = C * k * (t - t₀) := by ring
  rw [h_rhs_exp] at h_mul

  exact h_mul

theorem persistence_lemma_clean
  {E : ℝ → ℝ} {C k c₁ ε t₀ : ℝ}
  (hC : C > 0) (hk : k > 0) (hc₁ : c₁ > 0) (hε : ε > 0)
  (h_small : C * c₁ ≤ 1/2)
  (h_diff : ∀ t ≥ t₀, DifferentiableAt ℝ E t)
  (h_nonneg : ∀ t ≥ t₀, E t ≥ 0)
  (h_deriv : ∀ t ≥ t₀, deriv E t ≤ C * k * E t)
  (h_init : E t₀ ≤ ε) :
  ∀ t ∈ Set.Icc t₀ (t₀ + c₁/k), E t ≤ 2 * ε := by

  intro t ht
  have h_diff_on : DifferentiableOn ℝ E (Set.Ici t₀) := fun x hx => (h_diff x hx).differentiableWithinAt

  have h_gronwall := gronwall_exponential_bound hC hk hε h_diff_on h_nonneg h_deriv h_init t ht.1

  have h_time : t - t₀ ≤ c₁ / k := by linarith [ht.2]

  have h_exp_arg : C * k * (t - t₀) ≤ C * c₁ := by
    calc C * k * (t - t₀)
      ≤ C * k * (c₁ / k) := mul_le_mul_of_nonneg_left h_time (mul_nonneg (le_of_lt hC) (le_of_lt hk))
    _ = C * c₁ := by field_simp [ne_of_gt hk]

  have h_exp : exp (C * k * (t - t₀)) ≤ exp (C * c₁) := exp_le_exp.mpr h_exp_arg

  have h_le_half : exp (C * c₁) ≤ exp (1/2) := exp_le_exp.mpr h_small

  have h_final : exp (C * k * (t - t₀)) < 2 := by
    apply lt_of_le_of_lt h_exp
    apply lt_of_le_of_lt h_le_half
    exact exp_half_lt_two_clean

  -- Explicit calc-like steps
  have h_step1 : E t ≤ ε * exp (C * k * (t - t₀)) := h_gronwall

  have h_step2 : ε * exp (C * k * (t - t₀)) ≤ ε * 2 := by
    apply mul_le_mul_of_nonneg_left (le_of_lt h_final) (le_of_lt hε)

  have h_step3 : ε * 2 = 2 * ε := by ring

  rw [h_step3] at h_step2
  exact le_trans h_step1 h_step2
