#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Test with stop sequences to prevent markdown"""

from openai import OpenAI
import sys, codecs

if sys.platform == 'win32':
    sys.stdout = codecs.getwriter('utf-8')(sys.stdout.buffer, 'strict')

client = OpenAI(base_url="http://localhost:1234/v1", api_key="lm-studio")

# More explicit few-shot with ANTI-pattern
PROMPT = """CORRECT format (do this):
import Mathlib.Analysis.Calculus.Deriv.Basic

theorem even_square (n : ℕ) (h : Even n) : Even (n * n) := by
  obtain ⟨k, hk⟩ := h
  use 2 * k * k
  rw [hk]
  ring

WRONG format (do NOT do this):
### Theorem
```lean
theorem ...
```

---

Now write Lean 4 code for:

"Let k > 0, C > 0, c1 > 0, θ0 ≥ 0. Let τ = c1/k.
If θ : ℝ → ℝ is differentiable on [t0-τ, t0] with deriv θ t ≤ C*k*(θ t)²,
θ t0 ≤ θ0, and C*c1*θ0 ≤ 1/2, then θ t ≤ 2*θ0 for all t in [t0-τ, t0]."

import"""

print("Testing with anti-pattern example and leading 'import'...")

response = client.chat.completions.create(
    model="deepseek-prover-v2-7b",
    messages=[
        {"role": "system", "content": "Output only Lean 4 code. Start with 'import'. No markdown."},
        {"role": "user", "content": PROMPT}
    ],
    temperature=0.7,
    max_tokens=1024,
    extra_body={"repeat_penalty": 1.3},
    stop=["###", "```", "---", "WRONG", "CORRECT"],
    stream=False
)

result = "import" + response.choices[0].message.content

with open("C:/v2_files/lean_proofs/LHF_04_gronwall/LHF_04_v3.lean", 'w', encoding='utf-8') as f:
    f.write(result)

print(f"[{len(result)} chars] Saved to LHF_04_v3.lean")
print(f"Has import: {'import' in result}")
print(f"Has theorem: {'theorem' in result or 'lemma' in result}")
print(f"\nFirst 500 chars:\n{result[:500]}")
