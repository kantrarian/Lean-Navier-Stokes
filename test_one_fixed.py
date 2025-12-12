#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Test ONE proof with fixed parameters"""

from openai import OpenAI
import sys
import codecs

# Fix Windows encoding
if sys.platform == 'win32':
    sys.stdout = codecs.getwriter('utf-8')(sys.stdout.buffer, 'strict')

client = OpenAI(
    base_url="http://localhost:1234/v1",
    api_key="lm-studio"
)

FEW_SHOT = """Example Input: "Prove that the square of an even number is even."

Example Output:
import Mathlib.Data.Nat.Basic

theorem even_square (n : ℕ) (h : Even n) : Even (n * n) := by
  obtain ⟨k, hk⟩ := h
  use 2 * k * k
  rw [hk]
  ring
"""

GRONWALL_THEOREM = """Let k > 0, C > 0, c1 > 0, θ0 ≥ 0, and τ := c1 / k.

Suppose θ : ℝ → ℝ is differentiable on [t0 - τ, t0] and satisfies:
  - θ(t) ≥ 0 for all t ∈ [t0 - τ, t0]
  - deriv θ t ≤ C * k * (θ t)²
  - θ(t0) ≤ θ0
  - C * c1 * θ0 ≤ 1/2

Prove that for all t ∈ [t0 - τ, t0]: θ(t) ≤ 2 * θ0"""

print("="*80)
print("TESTING: LHF-04 Gronwall ODE with FIXED parameters")
print("  Temperature: 0.7 (was 0.1)")
print("  Repeat Penalty: 1.3 (new)")
print("  System Prompt: Code-only")
print("  User Prompt: Few-shot example")
print("="*80)

response = client.chat.completions.create(
    model="deepseek-prover-v2-7b",
    messages=[
        {
            "role": "system",
            "content": "You are a Lean 4 code generator. Do not output natural language. Do not output plans. Output only valid Lean 4 code."
        },
        {
            "role": "user",
            "content": f'{FEW_SHOT}\n\nNow translate this theorem:\n\nInput: "{GRONWALL_THEOREM}"\n\nOutput (Lean 4 code only):'
        }
    ],
    temperature=0.7,
    max_tokens=2048,
    extra_body={"repeat_penalty": 1.3},
    stream=False
)

result = response.choices[0].message.content

# Save FIRST before trying to print
with open("C:/v2_files/lean_proofs/LHF_04_gronwall/LHF_04_test.lean", 'w', encoding='utf-8') as f:
    f.write(result)

print(f"\n[RESPONSE: {len(result)} chars]")
print(f"[SAVED] C:/v2_files/lean_proofs/LHF_04_gronwall/LHF_04_test.lean\n")

# Validate
has_import = 'import' in result.lower()
has_theorem = 'theorem' in result or 'lemma' in result
lines = result.split('\n')
unique_ratio = len(set(lines)) / len(lines) if lines else 0

print(f"[VALIDATION]")
print(f"  Has imports: {'YES' if has_import else 'NO'}")
print(f"  Has theorem: {'YES' if has_theorem else 'NO'}")
print(f"  Unique lines: {unique_ratio:.1%} ({'GOOD' if unique_ratio > 0.7 else 'REPETITIVE'})")

if has_import and has_theorem and unique_ratio > 0.7:
    print(f"\n[SUCCESS] This looks good! Ready to run all 7.")
    print(f"\nTo see the code: cat C:/v2_files/lean_proofs/LHF_04_gronwall/LHF_04_test.lean")
else:
    print(f"\n[NEEDS WORK] May need more tuning.")
