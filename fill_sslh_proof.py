#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Skeleton Strategy: Ask DeepSeek to fill in ONLY the proof tactics
"""

from openai import OpenAI
import sys, codecs

if sys.platform == 'win32':
    sys.stdout = codecs.getwriter('utf-8')(sys.stdout.buffer, 'strict')

client = OpenAI(base_url="http://localhost:1234/v1", api_key="lm-studio")

# The FOCUSED prompt - just the theorem context and the proof state
PROOF_PROMPT = """You are completing a Lean 4 proof. Here is the theorem statement and context:

```lean
axiom curvature_transport_inequality (C₀ : ℝ) (ν : ℝ) :
  ∀ t, deriv Lambda_inf t ≤ (C₀ * (k_eff t)^2 * (Lambda_inf t)) - (ν * (k_eff t)^2 * (Lambda_inf t))

theorem sslh_implies_decay
  (C₀ ν : ℝ)
  (h_pos : C₀ > 0)
  (h_visc : ν > 0)
  (h_strict : C₀ < ν)
  (h_k_pos : ∀ t, k_eff t > 0)
  (h_L_pos : ∀ t, Lambda_inf t > 0) :
  ∀ t, deriv Lambda_inf t < 0 := by
  intro t
  have h_ineq := curvature_transport_inequality C₀ ν t
  -- Complete the proof from here
```

Current proof state after the `have`:
- Goal: `deriv Lambda_inf t < 0`
- h_ineq : `deriv Lambda_inf t ≤ (C₀ * (k_eff t)^2 * (Lambda_inf t)) - (ν * (k_eff t)^2 * (Lambda_inf t))`
- h_strict : `C₀ < ν`
- h_k_pos : `k_eff t > 0`
- h_L_pos : `Lambda_inf t > 0`

Complete the proof. Output ONLY the tactic lines (no 'by', no 'sorry'), starting after `have h_ineq`:"""

print("="*80)
print("SKELETON STRATEGY: Filling in SSLH proof")
print("="*80)

response = client.chat.completions.create(
    model="deepseek-prover-v2-7b",
    messages=[
        {
            "role": "system",
            "content": "You are a Lean 4 proof assistant. Output only proof tactics, one per line. No explanations, no markdown."
        },
        {
            "role": "user",
            "content": PROOF_PROMPT
        }
    ],
    temperature=0.7,
    max_tokens=512,
    extra_body={"repeat_penalty": 1.5},
    stream=False
)

tactics = response.choices[0].message.content.strip()

print(f"\n[GENERATED TACTICS: {len(tactics)} chars]\n")
print("="*80)
print(tactics)
print("="*80)

# Construct the complete proof
complete_proof = f"""import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.NormedSpace.Banach
import Mathlib.MeasureTheory.Integral.Bochner

variable {{V : Type}} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable (t : ℝ)
variable (Lambda_inf : ℝ → ℝ)
variable (k_eff : ℝ → ℝ)
variable (Lambda_2 : ℝ → ℝ)

def StrictSpectralLock (C₀ : ℝ) : Prop :=
  ∀ t, (Lambda_inf t) ≤ (Real.sqrt C₀) * (k_eff t) * (Lambda_2 t)

axiom curvature_transport_inequality (C₀ : ℝ) (ν : ℝ) :
  ∀ t, deriv Lambda_inf t ≤ (C₀ * (k_eff t)^2 * (Lambda_inf t)) - (ν * (k_eff t)^2 * (Lambda_inf t))

theorem sslh_implies_decay
  (C₀ ν : ℝ)
  (h_pos : C₀ > 0)
  (h_visc : ν > 0)
  (h_strict : C₀ < ν)
  (h_k_pos : ∀ t, k_eff t > 0)
  (h_L_pos : ∀ t, Lambda_inf t > 0) :
  ∀ t, deriv Lambda_inf t < 0 := by
  intro t
  have h_ineq := curvature_transport_inequality C₀ ν t
  {tactics}
"""

# Save the completed proof
output_file = "C:/v2_files/lean_proofs/SSLH_complete.lean"
with open(output_file, 'w', encoding='utf-8') as f:
    f.write(complete_proof)

print(f"\n[SAVED] {output_file}")

# Quick validation
has_calc = 'calc' in tactics
has_linarith = 'linarith' in tactics or 'nlinarith' in tactics
has_ring = 'ring' in tactics
has_apply = 'apply' in tactics or 'exact' in tactics
has_have = 'have' in tactics

print(f"\n[TACTICS USED]")
print(f"  calc: {'YES' if has_calc else 'NO'}")
print(f"  linarith/nlinarith: {'YES' if has_linarith else 'NO'}")
print(f"  ring: {'YES' if has_ring else 'NO'}")
print(f"  apply/exact: {'YES' if has_apply else 'NO'}")
print(f"  have (intermediate): {'YES' if has_have else 'NO'}")

print(f"\n[NEXT STEP]")
print(f"1. Open {output_file} in VS Code with Lean 4")
print(f"2. Check if it compiles (orange squiggles = errors)")
print(f"3. If it works, we have a VERIFIED proof!")
print(f"4. If not, we iterate on the prompt")
