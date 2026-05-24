import LHF_04_gronwall.LHF_04_CLEAN

/-!
# LHF-04: Gronwall Inequality (Physical Interface)

This file defines the physical axiom used by the Navier-Stokes regularity program
and connects it to the clean mathematical proofs in `LHF_04_CLEAN.lean`.
-/

open Real Set

/-- Numerical fact: exp(1/2) < 2. True since exp(0.5) ≈ 1.6487.
    Patched 2026-05-23: this previously-axiomatized fact is now a theorem alias
    to the proved `exp_half_lt_two_clean` in LHF_04_CLEAN. -/
theorem exp_half_lt_two : Real.exp (1/2) < 2 := exp_half_lt_two_clean

namespace LHF_04_manual

/--
Main Theorem: Persistence of Energy Control

Given:
1. Constants C, k, c₁, ε > 0
2. Smallness condition: C * c₁ ≤ 1/2
3. Energy E(t) is differentiable and non-negative (from PDE existence)
4. Initial condition: E(t₀) ≤ ε
5. Energy growth bound: deriv E t ≤ C * k * E t (from OBL-007 derivation)

Then:
E(t) ≤ 2ε for all t in [t₀, t₀ + c₁/k].
-/
theorem persistence_of_regularity
  {E : ℝ → ℝ} {C k c₁ ε t₀ : ℝ}
  (hC : C > 0) (hk : k > 0) (hc₁ : c₁ > 0) (hε : ε > 0)
  (h_small : C * c₁ ≤ 1/2)
  (h_diff : ∀ t ≥ t₀, DifferentiableAt ℝ E t)
  (h_nonneg : ∀ t ≥ t₀, E t ≥ 0)
  (h_energy : ∀ t, DifferentiableAt ℝ E t → deriv E t ≤ C * k * E t)
  (h_init : E t₀ ≤ ε) :
  ∀ t ∈ Set.Icc t₀ (t₀ + c₁/k), E t ≤ 2 * ε := by

  -- Apply the clean persistence lemma
  apply persistence_lemma_clean hC hk hc₁ hε h_small h_diff h_nonneg
  · -- Prove the derivative bound using the energy growth hypothesis
    intro t ht
    exact h_energy t (h_diff t ht)
  · -- Initial condition
    exact h_init

end LHF_04_manual
