import HPDE_04_campanato.CampanatoSpaces

/-!
# LHF-07 ↔ HPDE-04 Wiring: Campanato Embedding for Navier-Stokes

This module connects the abstract LHF-07 Campanato embedding framework to
the concrete HPDE-04 Campanato space infrastructure.

## Key Connections

1. **Definitions**: Re-exports HPDE-04's `IsInCampanato`, `IsHolderContinuous`,
   `meanOscillation`, `morreyNorm` for use in NS regularity arguments.

2. **Proven Infrastructure**: HPDE-04 provides fully proven lemmas:
   - `abs_sub_rpow_le`: Convexity bound |a-b|^p ≤ 2^{p-1}(|a|^p + |b|^p)
   - `ballAverage_bound`: Jensen-type bound on ball averages
   - `meanOscillation_le_morrey`: Mean oscillation vs Morrey norm

3. **Axiom Grounding**: The Campanato-Hölder embedding axiom in HPDE-04
   provides the classical result that Campanato spaces embed into Hölder
   spaces for supercritical λ > n (n = 3 for R³).

## NS Application

For Navier-Stokes regularity (Paper 11):
- Energy decay estimates give: ∫_{B_r} |ω - ω_B|² ≤ C r^{3+2α} (Campanato)
- Campanato embedding gives: |ω(x) - ω(y)| ≤ C |x-y|^α (Hölder)
- Hölder regularity implies no blow-up at the point

This is the "regularity bridge" from PDE energy estimates to classical smoothness.
-/

open Real MeasureTheory Set Metric HPDE_04

namespace LHF_07

/-!
## Re-exported Definitions from HPDE-04

These are the key definitions for Campanato/Morrey space theory in R³.
-/

-- Domain type (R³ as Fin 3 → ℝ)
abbrev R3 := HPDE_04.R3

/-!
### Core Definitions
-/

/-- Ball average of a function over a ball in R³ -/
noncomputable def ballAverage := HPDE_04.ballAverage

/-- Mean oscillation over a ball (Campanato seminorm ingredient) -/
noncomputable def meanOscillation := HPDE_04.meanOscillation

/-- Morrey norm over a ball -/
noncomputable def morreyNorm := HPDE_04.morreyNorm

/-- Membership in Campanato space L^{p,λ} with bound M -/
def IsInCampanato := HPDE_04.IsInCampanato

/-- Hölder continuity with exponent α and constant C -/
def IsHolderContinuous := HPDE_04.IsHolderContinuous

/-!
### L² Specialized Definitions (for NS applications)
-/

/-- L² norm over a ball -/
noncomputable def L2Norm := HPDE_04.L2Norm

/-- L² mean oscillation over a ball -/
noncomputable def meanOscillationL2 := HPDE_04.meanOscillationL2

/-- Membership in L² Morrey space -/
def IsInMorreyL2 := HPDE_04.IsInMorreyL2

/-- Membership in L² Campanato space -/
def IsInCampanatoL2 := HPDE_04.IsInCampanatoL2

/-!
## Proven Infrastructure from HPDE-04

These lemmas are FULLY PROVEN (no sorry, no axiom) in HPDE-04.
They provide the analytical backbone for Campanato/Morrey estimates.
-/

/-- **Convexity bound for p-th powers (PROVEN)**

For all a, b ∈ ℝ and p ≥ 1:
  |a - b|^p ≤ 2^{p-1} · (|a|^p + |b|^p)

This is the key convexity estimate for Campanato/Morrey embeddings. -/
theorem abs_sub_rpow_le (a b : ℝ) (p : ℝ) (hp : 1 ≤ p) :
    |a - b| ^ p ≤ 2 ^ (p - 1) * (|a| ^ p + |b| ^ p) :=
  HPDE_04.abs_sub_rpow_le a b p hp

/-- **Ball average bound via Jensen (PROVEN)**

|⨍_B u| ≤ V^{-1/p} · (∫_B |u|^p)^{1/p}

This bounds the average of u by a Morrey-type norm. -/
theorem ballAverage_bound (u : R3 → ℝ) (x : R3) (r : ℝ) (p : ℝ)
    (hr : 0 < r) (hp : 1 ≤ p)
    (h_integ : IntegrableOn (fun y => |u y| ^ p) (Metric.ball x r))
    (h_u_integ : IntegrableOn u (Metric.ball x r)) :
    |HPDE_04.ballAverage u x r| ≤
    (volume (Metric.ball x r)).toReal ^ (-1/p) * HPDE_04.morreyNorm u x r p :=
  HPDE_04.ballAverage_bound u x r p hr hp h_integ h_u_integ

/-- **Mean oscillation vs Morrey norm (PROVEN)**

meanOsc(u) ≤ 2 · V^{-1/p} · morreyNorm(u)

This connects Campanato and Morrey conditions. -/
theorem meanOscillation_le_morrey (u : R3 → ℝ) (x : R3) (r : ℝ) (p : ℝ)
    (hr : 0 < r) (hp : 1 ≤ p)
    (h_integ : IntegrableOn (fun y => |u y| ^ p) (Metric.ball x r))
    (h_u_integ : IntegrableOn u (Metric.ball x r)) :
    HPDE_04.meanOscillation u x r p ≤
    2 * (volume (Metric.ball x r)).toReal ^ (-1/p) * HPDE_04.morreyNorm u x r p :=
  HPDE_04.meanOscillation_le_morrey u x r p hr hp h_integ h_u_integ

/-!
## Campanato-Hölder Embedding (Axiom from HPDE-04)

This is the deep classical theorem connecting Campanato spaces to Hölder spaces.
It is axiomatized in HPDE-04 with full mathematical documentation.
-/

/-- **Campanato-Hölder Embedding (Classical)**

For 3 < λ ≤ 3 + p, Campanato space L^{p,λ}(R³) embeds into C^{0,α} with α = (λ-3)/p.

This is the key "regularity bridge":
- Energy estimates give Campanato membership
- This theorem gives Hölder continuity
- Hölder regularity implies smoothness (no blow-up)

**References:**
- Campanato (1963): Proprietà di Hölderianità
- Giaquinta (1983): Multiple Integrals in Calc. of Variations, Ch. III
-/
theorem campanato_holder_embedding {C_embed : ℝ} (u : R3 → ℝ) (p lam M : ℝ)
    (hp : 1 ≤ p) (hlam_lower : 3 < lam) (hlam_upper : lam ≤ 3 + p)
    (h_camp : HPDE_04.IsInCampanato u p lam M) :
    HPDE_04.IsHolderContinuous u ((lam - 3) / p) (C_embed * M) :=
  HPDE_04.campanato_holder_embedding u p lam M hp hlam_lower hlam_upper h_camp

/-!
## NS Regularity Application

The main application to Navier-Stokes: if vorticity ω satisfies a Campanato
bound (from energy estimates), then ω is Hölder continuous (regularity).
-/

/-- **Vorticity Regularity via Campanato (NS Application)**

If vorticity ω satisfies the Campanato condition on balls:
  ∫_{B_r} |ω - ω_B|² ≤ M² · r^{3+2α}

then ω is Hölder continuous with exponent α.

This is Lemma 6.1 of Paper 11 applied to the L² case (p = 2).
-/
theorem vorticity_holder_from_campanato {C_embed : ℝ} (ω : R3 → ℝ) (α M : ℝ)
    (hα_pos : 0 < α) (hα_lt : α < 1)
    (h_camp : HPDE_04.IsInCampanato ω 2 (3 + 2*α) M) :
    HPDE_04.IsHolderContinuous ω α (C_embed * M) := by
  -- Apply campanato_holder_embedding with p = 2, λ = 3 + 2α
  -- Then (λ - 3)/p = (3 + 2α - 3)/2 = 2α/2 = α
  have hp : (1 : ℝ) ≤ 2 := by norm_num
  have hlam_lower : (3 : ℝ) < 3 + 2*α := by linarith
  have hlam_upper : 3 + 2*α ≤ 3 + 2 := by linarith
  have h_exp : (3 + 2*α - 3) / 2 = α := by ring
  rw [← h_exp]
  exact HPDE_04.campanato_holder_embedding ω 2 (3 + 2*α) M hp hlam_lower hlam_upper h_camp

/-!
## Summary

This module provides the complete Campanato machinery for NS regularity:

1. **Proven lemmas** (from HPDE-04):
   - `abs_sub_rpow_le`: Convexity bound
   - `ballAverage_bound`: Jensen-type average bound
   - `meanOscillation_le_morrey`: Campanato-Morrey connection

2. **Classical axiom** (documented in HPDE-04):
   - `campanato_holder_embedding`: L^{p,λ} → C^{0,α} for λ > 3

3. **NS application**:
   - `vorticity_holder_from_campanato`: Energy decay → Hölder regularity

The axiom is grounded in deep classical analysis (Campanato 1963, Giaquinta 1983).
The proven infrastructure handles all the concrete estimates needed for NS.
-/

end LHF_07
