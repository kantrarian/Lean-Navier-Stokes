from pathlib import Path
import re

p = Path(r"C:\v2_files\lean_proofs\HPDE_01_caccioppoli\HPDE_01_caccioppoli\EllipticCaccioppoli.lean")
text = p.read_text(encoding="utf-8")

# 1) Make gradientSq use (1 : â„) explicitly
text = re.sub(
    r"\(Pi\.single i 1\)\)\^2",
    "(Pi.single i (1 : â„)))^2",
    text,
    count=1,
)
# also fix other occurrences of Pi.single i 1 in the early block (safe local change)
text = text.replace("Pi.single i 1)", "Pi.single i (1 : â„))")
text = text.replace("Pi.single i 1 : Fin 3 â†’ â„", "Pi.single i (1 : â„) : Fin 3 â†’ â„")

# 2) Rewrite gradientSq_le_three_mul_fderiv_norm_sq to avoid abs/norm mismatch
m = re.search(r"lemma gradientSq_le_three_mul_fderiv_norm_sq[\s\S]*?\n\n", text)
# replace by finding from lemma start to just before next doc comment '/-- The operator norm squared'
start = text.find("lemma gradientSq_le_three_mul_fderiv_norm_sq")
marker = text.find("/-- The operator norm squared is bounded by 3 times gradientSq.")
if start != -1 and marker != -1 and start < marker:
    replacement = """lemma gradientSq_le_three_mul_fderiv_norm_sq (f : (Fin 3 â†’ â„) â†’ â„) (x : Fin 3 â†’ â„) :
    gradientSq f x â‰¤ 3 * â€–fderiv â„ f xâ€–^2 := by
  unfold gradientSq
  by_cases hf : DifferentiableAt â„ f x
  Â· have h_bound : âˆ€ i : Fin 3, â€–fderiv â„ f x (Pi.single i (1 : â„))â€–^2 â‰¤ â€–fderiv â„ f xâ€–^2 := fun i => by
      have h1 : â€–fderiv â„ f x (Pi.single i (1 : â„))â€– â‰¤ â€–fderiv â„ f xâ€– * â€–(Pi.single i (1 : â„) : Fin 3 â†’ â„)â€– :=
        ContinuousLinearMap.le_opNorm _ _
      rw [norm_pi_single_one i] at h1
      rw [mul_one] at h1
      exact sq_le_sq' (by simpa using (norm_nonneg (fderiv â„ f x (Pi.single i (1 : â„))))) h1
    calc âˆ‘ i : Fin 3, â€–fderiv â„ f x (Pi.single i (1 : â„))â€–^2
      â‰¤ âˆ‘ i : Fin 3, â€–fderiv â„ f xâ€–^2 := Finset.sum_le_sum (fun i _ => h_bound i)
      _ = 3 * â€–fderiv â„ f xâ€–^2 := by simp
  Â· simp [fderiv_zero_of_not_differentiableAt hf, gradientSq]

"""
    text = text[:start] + replacement + text[marker:]

# 3) Make the fderiv_norm... axiom a clean block (remove leftover bullets)
ax = "axiom fderiv_norm_sq_le_three_mul_gradientSq"
start = text.find(ax)
marker = text.find("/-!\n## Helper Lemmas for Caccioppoli")
if start != -1 and marker != -1 and start < marker:
    # keep axiom statement up to its line, then jump to marker
    # find end of axiom statement block by taking up to the first blank line after it
    after = text.find("\n\n", start)
    if after == -1:
        after = start
    axiom_block = text[start:after].rstrip() + "\n\n"
    text = text[:start] + axiom_block + text[marker:]

p.write_text(text, encoding="utf-8")
print("fix_hpde01_blocks_compile applied")