#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
DeepSeek Prover V2 Sprint Runner - FIXED VERSION
With proper temperature, repeat_penalty, and few-shot prompting
"""

from openai import OpenAI
import json
import time
from pathlib import Path
import sys

if sys.platform == 'win32':
    import codecs
    sys.stdout = codecs.getwriter('utf-8')(sys.stdout.buffer, 'strict')

LM_STUDIO_PORT = 1234
client = OpenAI(
    base_url=f"http://localhost:{LM_STUDIO_PORT}/v1",
    api_key="lm-studio"
)

BASE_DIR = Path("C:/v2_files/lean_proofs")

# FEW-SHOT EXAMPLE to show the model what we want
FEW_SHOT_EXAMPLE = """Example Input: "Prove that the square of an even number is even."

Example Output:
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Basic

theorem even_square (n : ℕ) (h : Even n) : Even (n * n) := by
  obtain ⟨k, hk⟩ := h
  use 2 * k * k
  rw [hk]
  ring
"""

TASKS = [
    {
        "id": "LHF_01",
        "name": "Matrix Commutator Algebra",
        "dir": "LHF_01_commutator",
        "theorem": """Let A, B be 3×3 real matrices. Define the commutator [A,B] = A⬝B - B⬝A.
Assume A = S + Ω where S is symmetric (Sᵀ = S) and Ω is skew-symmetric (Ωᵀ = -Ω).

Prove the identity:
trace((commutator A B)ᵀ ⬝ (commutator A B)) =
  trace((commutator S B)ᵀ ⬝ (commutator S B)) +
  trace((commutator Ω B)ᵀ ⬝ (commutator Ω B)) +
  2 * trace((commutator S B)ᵀ ⬝ (commutator Ω B))

Use matrices indexed by Fin 3 over ℝ."""
    },
    {
        "id": "LHF_02",
        "name": "GKT Scaling Invariance",
        "dir": "LHF_02_gkt_scaling",
        "theorem": """For a measurable function ω : ℝ³ × ℝ → ℝ, define the scaled function:
ω_λ(x,t) := λ² * ω(λ•x, λ²*t) for λ > 0

Define A_ω(r; 0,0) = (∫_{-r²}^0 (∫_{|x|<r} |ω(x,t)|³ dx)^(2/3) dt)^(1/2)

Prove that for λ > 0 and r > 0:
A_{ω_λ}(r; 0,0) = A_ω(λ*r; 0,0)

using change of variables in integrals."""
    },
    {
        "id": "LHF_03",
        "name": "Toy Gaussian GKT Scaling",
        "dir": "LHF_03_gaussian",
        "theorem": """Let k > 0 and define ω(x,t) = k² * exp(-(k²) * ‖x‖²) on ℝ³ × ℝ, independent of t.

Assume ∫_{|x| < r} |ω(x,t)|³ dx = C1 * k⁶ * r³ for some constant C1 > 0.

Define A_ω(r)² = ∫_{-r²}^0 (∫_{|x| < r} |ω(x,t)|³ dx)^(2/3) dt

Prove that there exists a constant C such that:
A_ω(r) = C * k² * r²"""
    },
    {
        "id": "LHF_04",
        "name": "Gronwall ODE for Rotor Coherence",
        "dir": "LHF_04_gronwall",
        "theorem": """Let k > 0, C > 0, c1 > 0, θ0 ≥ 0, and τ := c1 / k.

Suppose θ : ℝ → ℝ is differentiable on [t0 - τ, t0] and satisfies:
  - θ(t) ≥ 0 for all t ∈ [t0 - τ, t0]
  - deriv θ t ≤ C * k * (θ t)²
  - θ(t0) ≤ θ0
  - C * c1 * θ0 ≤ 1/2

Prove that for all t ∈ [t0 - τ, t0]: θ(t) ≤ 2 * θ0"""
    },
    {
        "id": "LHF_05",
        "name": "Gagliardo-Nirenberg L³ Inequality",
        "dir": "LHF_05_gagliardo",
        "theorem": """Let f : ℝ³ → ℝ be a smooth compactly supported function.

Prove the Gagliardo-Nirenberg inequality:
‖f‖_{L³(ℝ³)} ≤ C * (‖f‖_{L²(ℝ³)})^(1/2) * (‖∇f‖_{L²(ℝ³)})^(1/2)

for some universal constant C."""
    },
    {
        "id": "LHF_06",
        "name": "Log-Sobolev for Standard Gaussian",
        "dir": "LHF_06_logsobolev",
        "theorem": """Let γ be the standard Gaussian measure on ℝⁿ (density ∝ exp(-‖x‖²/2)).
Let f : ℝⁿ → ℝ be a smooth, compactly supported function.

State the Gaussian log-Sobolev inequality:
∫ f² log(f²) dγ - (∫ f² dγ) * log(∫ f² dγ) ≤ 2 * ∫ ‖∇f‖² dγ

Define the entropy functional and provide the lemma statement."""
    },
    {
        "id": "LHF_07",
        "name": "Campanato → Hölder",
        "dir": "LHF_07_campanato",
        "theorem": """Let F : ℝ³ → ℝ be a locally square-integrable function.
For x0 ∈ ℝ³ and r > 0, assume there exists C0 > 0 and α ∈ (0,1) such that for all 0 < ρ ≤ r:

(1/ρ³) * ∫_{B_ρ(x0)} (F(x) - F_{B_ρ})² dx ≤ C0 * (ρ/r)^(2*α)

where F_{B_ρ} = (1/|B_ρ|) ∫_{B_ρ(x0)} F(y) dy.

Prove that F is Hölder continuous of exponent α on B_{r/2}(x0):
∃ C > 0, ∀ x,y ∈ B_{r/2}(x0), |F(x) - F(y)| ≤ C * ‖x - y‖^α"""
    }
]


def query_deepseek_fixed(theorem: str, task_id: str) -> str:
    """Query DeepSeek with FIXED parameters - no more loops!"""
    print(f"\n{'='*80}")
    print(f"Querying DeepSeek Prover for {task_id}...")
    print(f"{'='*80}\n")

    # Build the user prompt with few-shot example
    user_prompt = f"""{FEW_SHOT_EXAMPLE}

Now translate this theorem into Lean 4 code:

Input: "{theorem}"

Output (Lean 4 code only):"""

    try:
        response = client.chat.completions.create(
            model="deepseek-prover-v2-7b",
            messages=[
                {
                    "role": "system",
                    "content": "You are a Lean 4 code generator. Do not output natural language. Do not output plans. Do not output explanations. Output only valid Lean 4 code with imports and theorem statements."
                },
                {
                    "role": "user",
                    "content": user_prompt
                }
            ],
            temperature=0.7,        # FIXED: Was 0.1, now 0.7
            max_tokens=4096,
            extra_body={            # FIXED: Added repeat_penalty
                "repeat_penalty": 1.3
            },
            stream=False
        )

        result = response.choices[0].message.content
        print(f"[OK] Received response ({len(result)} chars)")
        return result

    except Exception as e:
        print(f"[ERROR] Error querying DeepSeek: {e}")
        return f"-- ERROR: {e}\n-- Could not generate proof for {task_id}"


def save_proof(content: str, task_dir: str, task_id: str):
    """Save Lean proof to file"""
    dir_path = BASE_DIR / task_dir
    dir_path.mkdir(parents=True, exist_ok=True)

    lean_file = dir_path / f"{task_id}_v2.lean"

    with open(lean_file, 'w', encoding='utf-8') as f:
        f.write(content)

    print(f"[OK] Saved to: {lean_file}")


def run_sprint_fixed():
    """Execute all 7 LHF tasks with FIXED parameters"""
    print(f"\n{'#'*80}")
    print("# DeepSeek Prover V2 - NS Regularity Sprint (FIXED VERSION)")
    print("# Temperature: 0.7, Repeat Penalty: 1.3, Few-Shot Prompting")
    print(f"{'#'*80}\n")

    results = []

    for i, task in enumerate(TASKS, 1):
        print(f"\n\n{'='*80}")
        print(f"= Task {i}/7: {task['name']}")
        print(f"= ID: {task['id']}")
        print(f"{'='*80}\n")

        # Query DeepSeek Prover with FIXED settings
        lean_code = query_deepseek_fixed(task['theorem'], task['id'])

        # Save result
        save_proof(lean_code, task['dir'], task['id'])

        # Check quality
        has_import = 'import' in lean_code.lower()
        has_theorem = 'theorem' in lean_code or 'lemma' in lean_code or 'def' in lean_code
        lines = lean_code.split('\n')
        unique_lines = set(lines)
        repetition_ratio = len(unique_lines) / len(lines) if lines else 0

        results.append({
            'task_id': task['id'],
            'name': task['name'],
            'success': has_import and has_theorem and repetition_ratio > 0.5,
            'file': f"{task['dir']}/{task['id']}_v2.lean",
            'length': len(lean_code),
            'has_import': has_import,
            'has_theorem': has_theorem,
            'repetition_ratio': round(repetition_ratio, 2)
        })

        # Brief pause between queries
        if i < len(TASKS):
            time.sleep(1)

    # Print summary
    print(f"\n\n{'='*80}")
    print("SPRINT SUMMARY (FIXED VERSION)")
    print(f"{'='*80}\n")

    success_count = 0
    for i, result in enumerate(results, 1):
        status = "[OK]" if result['success'] else "[FAIL]"
        if result['success']:
            success_count += 1
        print(f"{status} {i}. {result['name']}")
        print(f"   File: {result['file']} ({result['length']} chars)")
        print(f"   Quality: Import={'Y' if result['has_import'] else 'N'}, "
              f"Theorem={'Y' if result['has_theorem'] else 'N'}, "
              f"Unique={result['repetition_ratio']}")

    # Save summary JSON
    summary_file = BASE_DIR / "sprint_summary_v2.json"
    with open(summary_file, 'w') as f:
        json.dump({
            'timestamp': time.strftime('%Y-%m-%d %H:%M:%S'),
            'total_tasks': len(TASKS),
            'successful': success_count,
            'success_rate': f"{success_count}/{len(TASKS)}",
            'results': results,
            'improvements': {
                'temperature': '0.7 (was 0.1)',
                'repeat_penalty': '1.3 (was none)',
                'prompting': 'Few-shot example added',
                'system_prompt': 'Code-only, no plans'
            }
        }, f, indent=2)

    print(f"\n[OK] Summary saved to: {summary_file}")
    print(f"\nSuccess Rate: {success_count}/{len(TASKS)}")
    print(f"{'='*80}\n")


if __name__ == "__main__":
    try:
        run_sprint_fixed()
    except KeyboardInterrupt:
        print("\n\nSprint interrupted by user.")
    except Exception as e:
        print(f"\n\nFatal error: {e}")
        raise
