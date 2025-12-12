#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Skeleton Strategy V2: Few-shot with similar completed proof"""

from openai import OpenAI
import sys, codecs

if sys.platform == 'win32':
    sys.stdout = codecs.getwriter('utf-8')(sys.stdout.buffer, 'strict')

client = OpenAI(base_url="http://localhost:1234/v1", api_key="lm-studio")

# FEW-SHOT: Show a SIMILAR completed proof first
FEW_SHOT_EXAMPLE = """EXAMPLE of a completed proof:

```lean
-- Similar problem: If a ≤ b - c and c > 0 and b < 0, then a < 0
theorem example_negative
  (a b c : ℝ)
  (h_ineq : a ≤ b - c)
  (h_c_pos : c > 0)
  (h_b_neg : b < 0) :
  a < 0 := by
  have h1 : b - c < 0 := by linarith
  linarith
```

Notice: The proof uses `have` for an intermediate step, then `linarith` to finish.
"""

# The ACTUAL problem to solve
SSLH_PROBLEM = """NOW solve this similar problem:

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
```

Complete ONLY the proof tactics after `have h_ineq`. Output tactics only, one per line."""

FULL_PROMPT = FEW_SHOT_EXAMPLE + "\n" + SSLH_PROBLEM

print("="*80)
print("V2: Few-shot with similar completed proof")
print("="*80)

response = client.chat.completions.create(
    model="deepseek-prover-v2-7b",
    messages=[
        {
            "role": "system",
            "content": "You complete Lean 4 proofs. Output only tactic commands, no explanations."
        },
        {
            "role": "user",
            "content": FULL_PROMPT
        }
    ],
    temperature=0.6,
    max_tokens=256,
    extra_body={"repeat_penalty": 1.8},
    stream=False
)

tactics = response.choices[0].message.content.strip()

print(f"\n[TACTICS: {len(tactics)} chars]\n")
print(tactics)

# Build complete file
complete_proof = f"""import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.NormedSpace.Banach

variable {{V : Type}} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable (t : ℝ) (Lambda_inf k_eff Lambda_2 : ℝ → ℝ)

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

with open("C:/v2_files/lean_proofs/SSLH_v2.lean", 'w', encoding='utf-8') as f:
    f.write(complete_proof)

print(f"\n[SAVED] SSLH_v2.lean")
print(f"\nCheck for valid tactics: linarith={'YES' if 'linarith' in tactics else 'NO'}, nlinarith={'YES' if 'nlinarith' in tactics else 'NO'}")
print(f"\nNext: Load SSLH_v2.lean in Lean 4 to verify it compiles!")
