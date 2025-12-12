#!/usr/bin/env python3
"""Final test: Maximum repeat penalty, minimal prompt"""

from openai import OpenAI
import sys, codecs

if sys.platform == 'win32':
    sys.stdout = codecs.getwriter('utf-8')(sys.stdout.buffer, 'strict')

client = OpenAI(base_url="http://localhost:1234/v1", api_key="lm-studio")

# ULTRA-SIMPLE prompt
SIMPLE_PROMPT = """Write Lean 4 code for Gronwall inequality:
If deriv θ t ≤ C*k*(θ t)² and θ t0 ≤ θ0 and C*c1*θ0 ≤ 1/2, then θ t ≤ 2*θ0.

import Mathlib.Analysis.Calculus.Deriv.Basic

theorem gronwall_bound"""

print("Final test: repeat_penalty=2.0, ultra-simple prompt...")

response = client.chat.completions.create(
    model="deepseek-prover-v2-7b",
    messages=[
        {"role": "system", "content": "Continue this Lean 4 code. Output only code, no text."},
        {"role": "user", "content": SIMPLE_PROMPT}
    ],
    temperature=0.8,
    max_tokens=1024,
    extra_body={"repeat_penalty": 2.0},  # MAXIMUM
    stream=False
)

result = SIMPLE_PROMPT.split('\n\n')[1] + response.choices[0].message.content

with open("C:/v2_files/lean_proofs/LHF_04_gronwall/LHF_04_v5.lean", 'w', encoding='utf-8') as f:
    f.write(result)

lines = result.split('\n')
unique = len(set(lines))
total = len(lines)
ratio = unique / total if total else 0

print(f"\n[{len(result)} chars, {unique}/{total} unique lines = {ratio:.1%}]\n")
print(result[:600])
print(f"\n{'[SUCCESS - NO LOOPS]' if ratio > 0.8 else '[STILL LOOPING]'}")
