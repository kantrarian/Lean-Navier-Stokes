#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
DeepSeek Prover V2 Sprint Runner
Executes 7 low-hanging fruit formal proofs for NS regularity theory
"""

from openai import OpenAI
import json
import time
from pathlib import Path
import sys

# Force UTF-8 output on Windows
if sys.platform == 'win32':
    import codecs
    sys.stdout = codecs.getwriter('utf-8')(sys.stdout.buffer, 'strict')

# LM Studio configuration - adjust port if needed
LM_STUDIO_PORT = 1234  # Default LM Studio port; change to 36798 if needed
client = OpenAI(
    base_url=f"http://localhost:{LM_STUDIO_PORT}/v1",
    api_key="lm-studio"  # Dummy key for local instance
)

# Base directory for proofs
BASE_DIR = Path("C:/v2_files/lean_proofs")

# Define all 7 LHF tasks
TASKS = [
    {
        "id": "LHF_01",
        "name": "Matrix Commutator Algebra",
        "dir": "LHF_01_commutator",
        "prompt": """You are an expert Lean 4 theorem prover using mathlib.

I want to prove a simple lemma about commutators of 3x3 real matrices.

Let A, B be 3x3 real matrices. Define the commutator [A,B] = A ⬝ B - B ⬝ A.
Assume A = S + Ω where S is symmetric (Sᵀ = S) and Ω is skew-symmetric (Ωᵀ = -Ω).

1. Define in Lean the commutator of two matrices.
2. Prove the identity:
   trace ((commutator A B)ᵀ ⬝ (commutator A B))
   =
   trace ((commutator S B)ᵀ ⬝ (commutator S B))
   +
   trace ((commutator Ω B)ᵀ ⬝ (commutator Ω B))
   +
   2 * trace ((commutator S B)ᵀ ⬝ (commutator Ω B)).

You can use matrices indexed by `fin 3` over `ℝ`. Please write the full Lean 4 code, including imports, definitions, and lemma."""
    },
    {
        "id": "LHF_02",
        "name": "GKT Scaling Invariance",
        "dir": "LHF_02_gkt_scaling",
        "prompt": """You are an expert Lean 4 theorem prover using mathlib and measure theory.

Consider ℝ³ × ℝ with coordinates (x,t) and a measurable function ω : ℝ³ × ℝ → ℝ.

Define the parabolic cylinder
  Q r (x0,t0) := { (x,t) | |x - x0| < r ∧ t0 - r^2 < t ∧ t ≤ t0 }.

Define the scaled function
  ω_λ (x,t) := λ^2 * ω (λ • x, λ^2 * t),
for λ > 0, where `•` is scalar multiplication on ℝ³.

Define
  A_ω(r; x0,t0) = ( ∫_{t0 - r^2}^{t0} ( ∫_{|x - x0| < r} |ω(x,t)|^3 dx )^{2/3} dt )^{1/2}.

1. Formalize these definitions in Lean in a simplified form where x0 = 0 and t0 = 0.
2. Prove that for λ > 0 and r > 0,
   A_{ω_λ}(r; 0,0) = A_ω(λ*r; 0,0),
using change of variables in integrals.

Please write Lean 4 code with the main lemma and sketch the necessary auxiliary lemmas (you may assume standard properties of Lebesgue measure and basic change-of-variable theorems)."""
    },
    {
        "id": "LHF_03",
        "name": "Toy Gaussian GKT Scaling",
        "dir": "LHF_03_gaussian",
        "prompt": """You are an expert Lean 4 theorem prover.

Let k > 0 and define ω(x,t) = k^2 * exp (-(k^2) * ∥x∥^2) on ℝ³ × ℝ, independent of t.

For r > 0, define
  A_ω(r)^2
  =
  ∫_{t = -r^2}^0 ( ∫_{|x| < r} |ω(x,t)|^3 dx )^{2/3} dt.

Assume we model the inner integral exactly (or up to a constant C) as
  ∫_{|x| < r} |ω(x,t)|^3 dx = C1 * k^6 * r^3
for some fixed constant C1 > 0, valid for r ≪ 1/k so that the Gaussian is approximately constant on the ball.

1. Formalize A_ω(r) with this approximated inner integral.
2. Prove that there exists a constant C such that
   A_ω(r) = C * k^2 * r^2.

You may abstract away the exact value of C and just prove the proportionality in k and r.
Write the main lemma in Lean 4, using real nonnegative integrals and simple algebra."""
    },
    {
        "id": "LHF_04",
        "name": "Gronwall ODE for Rotor Coherence",
        "dir": "LHF_04_gronwall",
        "prompt": """You are an expert Lean 4 theorem prover with mathlib.

Let k > 0, C > 0, c1 > 0, θ0 ≥ 0. Let τ := c1 / k.

Suppose θ : ℝ → ℝ is differentiable on [t0 - τ, t0] and satisfies:
  θ t ≥ 0 for all t ∈ [t0 - τ, t0],
  and for all t in this interval,
    deriv θ t ≤ C * k * (θ t)^2.

Assume θ t0 ≤ θ0 and C * c1 * θ0 ≤ 1/2.

Prove that for all t ∈ [t0 - τ, t0],
  θ t ≤ 2 * θ0.

This is a standard Gronwall-type estimate. Please write the Lean 4 lemma and proof, using basic real analysis tools from mathlib."""
    },
    {
        "id": "LHF_05",
        "name": "Gagliardo-Nirenberg L³ Inequality",
        "dir": "LHF_05_gagliardo",
        "prompt": """You are an expert Lean 4 theorem prover using mathlib's analysis library.

Let f : ℝ³ → ℝ be a smooth compactly supported function.

Prove a Gagliardo–Nirenberg type inequality:
  ∥f∥_{L^3(ℝ³)} ≤ C * (∥f∥_{L^2(ℝ³)})^(1/2) * (∥∇f∥_{L^2(ℝ³)})^(1/2)
for some universal constant C.

You may use any existing Sobolev or Gagliardo–Nirenberg lemmas in mathlib, or reduce to them. The main goal is to state this inequality in Lean and prove it (or derive it from an existing lemma).

Please provide the Lean statement and proof."""
    },
    {
        "id": "LHF_06",
        "name": "Log-Sobolev for Standard Gaussian",
        "dir": "LHF_06_logsobolev",
        "prompt": """You are an expert Lean 4 theorem prover.

Let γ be the standard Gaussian measure on ℝⁿ (density proportional to exp(-∥x∥²/2)).
Let f : ℝⁿ → ℝ be a smooth, compactly supported function.

State and (at least partially) prove the Gaussian log-Sobolev inequality:

  ∫ f^2 log (f^2) dγ
  - (∫ f^2 dγ) * log (∫ f^2 dγ)
  ≤ 2 * ∫ ∥∇f∥^2 dγ.

If full proof is too long, at least set up the measure, the entropy functional,
and reduce the inequality to a known result in mathlib, or outline the structure in Lean comments.

Please provide a Lean 4 definition of the entropy functional and the statement of the inequality as a lemma."""
    },
    {
        "id": "LHF_07",
        "name": "Campanato → Hölder",
        "dir": "LHF_07_campanato",
        "prompt": """You are an expert Lean 4 theorem prover.

Let F : ℝ³ → ℝ be a locally square-integrable function.
For x0 ∈ ℝ³ and r > 0, assume there exists C0 > 0 and α ∈ (0,1) such that
for all 0 < ρ ≤ r,

  (1 / ρ^3) * ∫_{B_ρ(x0)} (F(x) - F_{B_ρ})^2 dx
  ≤ C0 * (ρ / r)^{2 * α},

where F_{B_ρ} = (1 / |B_ρ|) ∫_{B_ρ(x0)} F(y) dy.

Prove that F is Hölder continuous of exponent α on B_{r/2}(x0), i.e.,

  ∃ C > 0, ∀ x,y ∈ B_{r/2}(x0),
    |F(x) - F(y)| ≤ C * ∥x - y∥^α.

This is a standard Campanato → Hölder lemma.
Please write the statement as a Lean lemma and either prove it or outline the key steps using existing mathlib results about Campanato and Hölder spaces."""
    }
]


def query_deepseek(prompt: str, task_id: str, max_tokens: int = 8192) -> str:
    """Query DeepSeek Prover via LM Studio API"""
    print(f"\n{'='*80}")
    print(f"Querying DeepSeek Prover for {task_id}...")
    print(f"{'='*80}\n")

    try:
        response = client.chat.completions.create(
            model="deepseek-prover-v2-7b",
            messages=[
                {
                    "role": "system",
                    "content": "You are DeepSeek Prover V2, a formal mathematics engine specializing in Lean 4. Output complete, compilable Lean 4 code with all necessary imports from mathlib. Be thorough and precise."
                },
                {
                    "role": "user",
                    "content": prompt
                }
            ],
            temperature=0.1,  # Low temperature for deterministic proofs
            max_tokens=max_tokens,
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

    lean_file = dir_path / f"{task_id}.lean"

    with open(lean_file, 'w', encoding='utf-8') as f:
        f.write(content)

    print(f"[OK] Saved to: {lean_file}")


def run_sprint():
    """Execute all 7 LHF tasks"""
    print(f"\n{'#'*80}")
    print("# DeepSeek Prover V2 - Navier-Stokes Regularity Sprint")
    print("# 7 Low-Hanging Fruit Formal Proofs")
    print(f"{'#'*80}\n")

    results = []

    for i, task in enumerate(TASKS, 1):
        print(f"\n\n{'='*80}")
        print(f"= Task {i}/7: {task['name']}")
        print(f"= ID: {task['id']}")
        print(f"{'='*80}\n")

        # Query DeepSeek Prover
        lean_code = query_deepseek(task['prompt'], task['id'])

        # Save result
        save_proof(lean_code, task['dir'], task['id'])

        results.append({
            'task_id': task['id'],
            'name': task['name'],
            'success': 'ERROR' not in lean_code[:100],
            'file': f"{task['dir']}/{task['id']}.lean",
            'length': len(lean_code)
        })

        # Brief pause between queries
        if i < len(TASKS):
            time.sleep(1)

    # Print summary
    print(f"\n\n{'='*80}")
    print("SPRINT SUMMARY")
    print(f"{'='*80}\n")

    for i, result in enumerate(results, 1):
        status = "[OK]" if result['success'] else "[FAIL]"
        print(f"{status} {i}. {result['name']}")
        print(f"   File: {result['file']} ({result['length']} chars)")

    # Save summary JSON
    summary_file = BASE_DIR / "sprint_summary.json"
    with open(summary_file, 'w') as f:
        json.dump({
            'timestamp': time.strftime('%Y-%m-%d %H:%M:%S'),
            'total_tasks': len(TASKS),
            'results': results
        }, f, indent=2)

    print(f"\n[OK] Summary saved to: {summary_file}")
    print(f"\n{'='*80}")
    print("Sprint complete! Next steps:")
    print("1. Review each .lean file")
    print("2. Verify with Lean 4 compiler: lean --version && lake build")
    print("3. Integrate into your NS regularity framework")
    print(f"{'='*80}\n")


if __name__ == "__main__":
    try:
        run_sprint()
    except KeyboardInterrupt:
        print("\n\nSprint interrupted by user.")
    except Exception as e:
        print(f"\n\nFatal error: {e}")
        raise
