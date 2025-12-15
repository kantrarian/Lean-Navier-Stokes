from pathlib import Path
import re

p = Path(r"C:\v2_files\lean_proofs\HPDE_01_caccioppoli\HPDE_01_caccioppoli\EllipticCaccioppoli.lean")
text = p.read_text(encoding="utf-8")

# 1) ensure import is present
imp = "import HPDE_01_caccioppoli.DualNorm\n"
if imp not in text:
    # insert after the last existing import line
    m = re.search(r"(^(?:import .*\n)+)", text, flags=re.MULTILINE)
    if not m:
        raise SystemExit("could not locate import block")
    insert_pos = m.end(1)
    text = text[:insert_pos] + imp + text[insert_pos:]

# helper to replace an axiom block by exact token name

def replace_axiom(name: str, replacement: str) -> None:
    global text
    # match `axiom name ... : ...` (until next blank line)
    pat = rf"axiom\s+{name}\b[\s\S]*?\n\n"
    new, n = re.subn(pat, replacement.rstrip() + "\n\n", text, count=1)
    if n != 1:
        raise SystemExit(f"failed to replace {name}, matches={n}")
    text = new

replace_axiom(
    "gradientSq_le_fderiv_norm_sq",
    """lemma gradientSq_le_fderiv_norm_sq (f : (Fin 3 â†’ â„) â†’ â„) (x : Fin 3 â†’ â„) :
    gradientSq f x â‰¤ â€–fderiv â„ f xâ€–^2 := by
  unfold gradientSq
  have hop : â€–fderiv â„ f xâ€– = âˆ‘ i : Fin 3, |(fderiv â„ f x) (Pi.single i (1 : â„))| := by
    simpa using (HPDE_01.opNorm_eq_sum_abs_fin3 (L := fderiv â„ f x))
  have h := HPDE_01.sum_sq_le_sq_sum_abs
    (a := fun i : Fin 3 => (fderiv â„ f x) (Pi.single i (1 : â„)))
  simpa [hop, pow_two] using h""",
)

replace_axiom(
    "gradientSq_le_three_mul_fderiv_norm_sq",
    """lemma gradientSq_le_three_mul_fderiv_norm_sq (f : (Fin 3 â†’ â„) â†’ â„) (x : Fin 3 â†’ â„) :
    gradientSq f x â‰¤ 3 * â€–fderiv â„ f xâ€–^2 := by
  have h := gradientSq_le_fderiv_norm_sq (f := f) (x := x)
  have h13 : (1 : â„) â‰¤ 3 := by norm_num
  have hc : 0 â‰¤ â€–fderiv â„ f xâ€–^2 := by exact sq_nonneg _
  have hmul : â€–fderiv â„ f xâ€–^2 â‰¤ 3 * â€–fderiv â„ f xâ€–^2 := by
    simpa [one_mul] using (mul_le_mul_of_nonneg_right h13 hc)
  exact le_trans h hmul""",
)

replace_axiom(
    "fderiv_norm_sq_le_three_mul_gradientSq",
    """lemma fderiv_norm_sq_le_three_mul_gradientSq (f : (Fin 3 â†’ â„) â†’ â„) (x : Fin 3 â†’ â„) :
    â€–fderiv â„ f xâ€–^2 â‰¤ 3 * gradientSq f x := by
  unfold gradientSq
  have hop : â€–fderiv â„ f xâ€– = âˆ‘ i : Fin 3, |(fderiv â„ f x) (Pi.single i (1 : â„))| := by
    simpa using (HPDE_01.opNorm_eq_sum_abs_fin3 (L := fderiv â„ f x))
  have h := HPDE_01.sq_sum_abs_le_three_mul_sum_sq
    (a := fun i : Fin 3 => (fderiv â„ f x) (Pi.single i (1 : â„)))
  simpa [hop, pow_two] using h""",
)

p.write_text(text, encoding="utf-8")
print("patched hpde01 axioms -> lemmas")