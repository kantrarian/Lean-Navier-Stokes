import LHF_04_gronwall.LHF_04_CLEAN
import LHF_04_gronwall.LHF_04_manual

/-!
# LHF-04: Gronwall Inequality

Main results:
- `gronwall_exponential_bound`: E(t) ≤ ε exp(Ck(t-t₀))
- `persistence_lemma_clean`: E(t) ≤ 2ε for t ∈ [t₀, t₀ + c₁/k]

The only axiom is `energy_inequality`: the physical input from NS.
-/
