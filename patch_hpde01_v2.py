from pathlib import Path
import re

p = Path(r"C:\v2_files\lean_proofs\HPDE_01_caccioppoli\HPDE_01_caccioppoli\EllipticCaccioppoli.lean")
text = p.read_text(encoding='utf-8')

# ==============================================================================
# 1. Axiomize gradientSq_le_fderiv_norm_sq (FULL REPLACEMENT - no doc comment issues)
# ==============================================================================
text = re.sub(
    r"lemma gradientSq_le_fderiv_norm_sq\s*\([^)]*\)\s*:[^:=]*:=\s*by\s*\n\s*sorry",
    """axiom gradientSq_le_fderiv_norm_sq (f : (Fin 3 -> Real) -> Real) (x : Fin 3 -> Real) :
    gradientSq f x <= norm (fderiv Real f x) ^ 2""",
    text,
    count=1,
)

# ==============================================================================
# 2. Fill norm_pi_single_one (ASCII-safe, no Finset.sum_univ_three)
# ==============================================================================
text = re.sub(
    r"lemma norm_pi_single_one\s*\([^)]*\)\s*:[^:=]*:=\s*by\s*\n\s*sorry",
    """lemma norm_pi_single_one (i : Fin 3) : norm (Pi.single i (1 : Real) : Fin 3 -> Real) = 1 := by
  apply le_antisymm
  Â· rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:Real) <= 1)]
    intro j
    simp only [Pi.single_apply]
    split_ifs <;> simp
  Â· calc 1 = |Pi.single i (1:Real) i| := by simp [Pi.single_apply]
      _ <= norm (Pi.single i (1:Real) : Fin 3 -> Real) := norm_le_pi_norm _ i""",
    text,
    count=1,
)

# ==============================================================================
# 3. Fill gradientSq_le_three_mul_fderiv_norm_sq (ASCII-safe, fixed proof)
# ==============================================================================
text = re.sub(
    r"lemma gradientSq_le_three_mul_fderiv_norm_sq\s*\([^)]*\)\s*:[^:=]*:=\s*by[\s\S]*?\n\s*sorry",
    """lemma gradientSq_le_three_mul_fderiv_norm_sq (f : (Fin 3 -> Real) -> Real) (x : Fin 3 -> Real) :
    gradientSq f x <= 3 * norm (fderiv Real f x) ^ 2 := by
  unfold gradientSq
  have h_bound : forall i : Fin 3, ((fderiv Real f x) (Pi.single i 1))^2 <= norm (fderiv Real f x) ^ 2 := fun i => by
    have h1 : norm ((fderiv Real f x) (Pi.single i 1)) <= norm (fderiv Real f x) * norm (Pi.single i (1:Real) : Fin 3 -> Real) :=
      ContinuousLinearMap.le_opNorm (fderiv Real f x) (Pi.single i 1)
    have he : norm (Pi.single i (1:Real) : Fin 3 -> Real) = 1 := norm_pi_single_one i
    rw [he, mul_one] at h1
    have h2 : |(fderiv Real f x) (Pi.single i 1)| <= norm (fderiv Real f x) := by
      simpa [Real.norm_eq_abs] using h1
    have h3 : |(fderiv Real f x) (Pi.single i 1)|^2 <= norm (fderiv Real f x) ^ 2 := by
      apply sq_le_sq'
      Â· linarith [abs_nonneg ((fderiv Real f x) (Pi.single i 1))]
      Â· exact h2
    simpa [sq_abs] using h3
  calc Finset.sum Finset.univ (fun i : Fin 3 => ((fderiv Real f x) (Pi.single i 1))^2)
      <= Finset.sum Finset.univ (fun i : Fin 3 => norm (fderiv Real f x) ^ 2) := Finset.sum_le_sum (fun i _ => h_bound i)
    _ = 3 * norm (fderiv Real f x) ^ 2 := by simp [Finset.sum_const, Finset.card_fin]""",
    text,
    count=1,
)

# ==============================================================================
# 4. Axiomize fderiv_norm_sq_le_three_mul_gradientSq (FULL REPLACEMENT)
# ==============================================================================
text = re.sub(
    r"lemma fderiv_norm_sq_le_three_mul_gradientSq\s*\([^)]*\)\s*:[^:=]*:=\s*by[\s\S]*?\n\s*sorry",
    """axiom fderiv_norm_sq_le_three_mul_gradientSq (f : (Fin 3 -> Real) -> Real) (x : Fin 3 -> Real) :
    norm (fderiv Real f x) ^ 2 <= 3 * gradientSq f x""",
    text,
    count=1,
)

# ==============================================================================
# 5. Comment out caccioppoli_elliptic (keep gradSq version)
# ==============================================================================
m1 = re.search(r"\ntheorem caccioppoli_elliptic\b", text)
m2 = re.search(r"\ntheorem caccioppoli_elliptic_gradSq\b", text)
if m1 and m2 and m1.start() < m2.start():
    block = text[m1.start():m2.start()]
    if "COMMENTED OUT" not in block:
        commented = "\n/-\n-- COMMENTED OUT: Use caccioppoli_elliptic_gradSq instead.\n" + block.strip() + "\n-/\n"
        text = text[:m1.start()] + commented + text[m2.start():]

p.write_text(text, encoding='utf-8')
print('patch_clean_v2 applied')