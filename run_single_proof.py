#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
DeepSeek Prover V2 - Single Proof Runner (Improved Prompting)
"""

from openai import OpenAI
import sys

client = OpenAI(
    base_url="http://localhost:1234/v1",
    api_key="lm-studio"
)

# IMPROVED PROMPT: Direct, code-focused, minimal meta-commentary
GRONWALL_PROMPT_V2 = """Write ONLY valid Lean 4 code. No explanations, no markdown, no comments outside the code.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp.Basic

-- Gronwall-type inequality for rotor coherence
-- Given: θ : ℝ → ℝ differentiable on [t0 - τ, t0]
-- Given: deriv θ t ≤ C * k * (θ t)^2
-- Given: θ t0 ≤ θ0 and C * c1 * θ0 ≤ 1/2 where τ = c1 / k
-- Prove: θ t ≤ 2 * θ0 for all t ∈ [t0 - τ, t0]

theorem gronwall_rotor_bound
  (k C c1 θ0 t0 : ℝ)
  (hk : 0 < k) (hC : 0 < C) (hc1 : 0 < c1) (hθ0 : 0 ≤ θ0)
  (θ : ℝ → ℝ)
  (hθ_diff : DifferentiableOn ℝ θ (Set.Icc (t0 - c1/k) t0))
  (hθ_nonneg : ∀ t ∈ Set.Icc (t0 - c1/k) t0, 0 ≤ θ t)
  (hθ_deriv : ∀ t ∈ Set.Icc (t0 - c1/k) t0, deriv θ t ≤ C * k * (θ t)^2)
  (hθ_t0 : θ t0 ≤ θ0)
  (hsmall : C * c1 * θ0 ≤ 1/2) :
  ∀ t ∈ Set.Icc (t0 - c1/k) t0, θ t ≤ 2 * θ0 := by
  sorry

-- Provide auxiliary lemmas if needed:"""

def test_single_proof():
    print("="*80)
    print("Testing LHF-04: Gronwall ODE (Improved Prompt)")
    print("="*80)

    try:
        response = client.chat.completions.create(
            model="deepseek-prover-v2-7b",
            messages=[
                {
                    "role": "system",
                    "content": "You are a Lean 4 code generator. Output ONLY valid Lean 4 code with proper imports and theorem statements. Never output markdown formatting or explanatory text outside of Lean comments."
                },
                {
                    "role": "user",
                    "content": GRONWALL_PROMPT_V2
                }
            ],
            temperature=0.3,
            max_tokens=2048,
            stop=["###", "```", "Step-by-step", "Abstract", "Explanation:"],
            stream=False
        )

        result = response.choices[0].message.content

        print(f"\n[RESPONSE LENGTH: {len(result)} chars]\n")
        print("="*80)
        print("GENERATED CODE:")
        print("="*80)
        print(result)
        print("="*80)

        # Save to file
        output_file = "C:/v2_files/lean_proofs/LHF_04_gronwall/LHF_04_v2.lean"
        with open(output_file, 'w', encoding='utf-8') as f:
            # Ensure imports are at top
            if not result.strip().startswith('import'):
                f.write(GRONWALL_PROMPT_V2.split('\n\n')[0] + '\n\n')
            f.write(result)

        print(f"\n[OK] Saved to: {output_file}")

        # Quick validation
        has_import = 'import' in result
        has_theorem = 'theorem' in result
        has_sorry = 'sorry' in result
        repetitive = len(set(result.split('\n'))) < len(result.split('\n')) * 0.5

        print(f"\n[VALIDATION]")
        print(f"  Has imports: {'YES' if has_import else 'NO'}")
        print(f"  Has theorem: {'YES' if has_theorem else 'NO'}")
        print(f"  Has sorry: {'YES (needs work)' if has_sorry else 'NO (complete!)'}")
        print(f"  Repetitive: {'YES (problem!)' if repetitive else 'NO (good)'}")

        if not repetitive and has_theorem:
            print(f"\n[SUCCESS] Generated valid Lean structure!")
            return True
        else:
            print(f"\n[FAILURE] Still has generation issues")
            return False

    except Exception as e:
        print(f"[ERROR] {e}")
        return False

if __name__ == "__main__":
    success = test_single_proof()
    sys.exit(0 if success else 1)
