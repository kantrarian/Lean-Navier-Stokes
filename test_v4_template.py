#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Template-filling approach - give skeleton, ask for tactics"""

from openai import OpenAI
import sys, codecs

if sys.platform == 'win32':
    sys.stdout = codecs.getwriter('utf-8')(sys.stdout.buffer, 'strict')

client = OpenAI(base_url="http://localhost:1234/v1", api_key="lm-studio")

# Provide a COMPLETE skeleton, ask only for proof tactics
TEMPLATE_PROMPT = """Complete this Lean 4 theorem by filling in the proof tactics (replace the sorry):

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Real.Basic

-- Gronwall-type bound for rotor coherence
theorem gronwall_rotor_bound
  {k C c1 θ0 t0 : ℝ}
  (hk : 0 < k) (hC : 0 < C) (hc1 : 0 < c1) (hθ0 : 0 ≤ θ0)
  (θ : ℝ → ℝ)
  (hθ_diff : DifferentiableOn ℝ θ (Set.Icc (t0 - c1/k) t0))
  (hθ_nonneg : ∀ t ∈ Set.Icc (t0 - c1/k) t0, 0 ≤ θ t)
  (hθ_deriv : ∀ t ∈ Set.Icc (t0 - c1/k) t0, deriv θ t ≤ C * k * (θ t)^2)
  (hθ_t0 : θ t0 ≤ θ0)
  (hsmall : C * c1 * θ0 ≤ 1/2) :
  ∀ t ∈ Set.Icc (t0 - c1/k) t0, θ t ≤ 2 * θ0 := by
  sorry

Fill in the proof (replace 'sorry' with actual tactics):"""

print("Testing template-filling approach...")

response = client.chat.completions.create(
    model="deepseek-prover-v2-7b",
    messages=[
        {
            "role": "system",
            "content": "You are completing a Lean 4 proof. Output the full theorem with the sorry replaced by actual proof tactics. Output only Lean code, no explanations."
        },
        {
            "role": "user",
            "content": TEMPLATE_PROMPT
        }
    ],
    temperature=0.6,
    max_tokens=2048,
    extra_body={"repeat_penalty": 1.2},
    stream=False
)

result = response.choices[0].message.content

with open("C:/v2_files/lean_proofs/LHF_04_gronwall/LHF_04_v4.lean", 'w', encoding='utf-8') as f:
    f.write(result)

print(f"\n[{len(result)} chars] Saved\n")

# Check if it's actual Lean code
has_import = result.count('import') >= 3
has_theorem = 'theorem gronwall_rotor_bound' in result
has_sorry = 'sorry' in result
has_tactics = any(tac in result for tac in ['intro', 'apply', 'exact', 'rw', 'simp', 'have', 'calc'])

print(f"[VALIDATION]")
print(f"  Has imports (3+): {'YES' if has_import else 'NO'}")
print(f"  Has theorem def: {'YES' if has_theorem else 'NO'}")
print(f"  Still has sorry: {'YES - incomplete' if has_sorry else 'NO - attempted proof'}")
print(f"  Has proof tactics: {'YES' if has_tactics else 'NO'}")

if has_import and has_theorem:
    print(f"\n[GOOD STRUCTURE] At least the skeleton is preserved!")
    if has_tactics and not has_sorry:
        print(f"[EXCELLENT] It attempted a full proof!")
    print(f"\nFirst 800 chars:\n{'-'*80}\n{result[:800]}")
else:
    print(f"\n[FAILED] Model didn't preserve structure")
