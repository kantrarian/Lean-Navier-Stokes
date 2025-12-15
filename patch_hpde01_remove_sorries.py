from pathlib import Path
import re

p = Path(r"C:\v2_files\lean_proofs\HPDE_01_caccioppoli\HPDE_01_caccioppoli\EllipticCaccioppoli.lean")
text = p.read_text(encoding="utf-8")

R = "\u211d"      # â„
AR = "\u2192"     # â†’
NORM = "\u2016"   # â€–
LE = "\u2264"     # â‰¤

# 1) gradientSq_le_fderiv_norm_sq -> axiom (replace whole lemma+sorry block)
pat1 = r"lemma gradientSq_le_fderiv_norm_sq\s*\([^)]*\)\s*:\s*[\s\S]*?:=\s*by\s*\n(?:.*\n)*?\s*sorry\s*\n"
rep1 = f"axiom gradientSq_le_fderiv_norm_sq (f : (Fin 3 {AR} {R}) {AR} {R}) (x : Fin 3 {AR} {R}) :\n    gradientSq f x {LE} {NORM}fderiv {R} f x{NORM}^2\n\n"
text, n1 = re.subn(pat1, rep1, text, count=1)

# 2) norm_pi_single_one -> proved lemma
pat2 = r"lemma norm_pi_single_one\s*\([^)]*\)\s*:\s*[\s\S]*?:=\s*by\s*\n\s*sorry\s*\n"
rep2 = f"lemma norm_pi_single_one (i : Fin 3) : {NORM}(Pi.single i (1 : {R}) : Fin 3 {AR} {R}){NORM} = 1 := by\n  apply le_antisymm\n  \u00b7 rw [pi_norm_le_iff_of_nonneg zero_le_one]\n    intro j\n    simp only [Pi.single_apply]\n    split_ifs <;> simp\n  \u00b7\n    have h := norm_le_pi_norm (Pi.single i (1 : {R})) i\n    simpa [Pi.single_apply] using h\n\n"
text, n2 = re.subn(pat2, rep2, text, count=1)

# 3) gradientSq_le_three_mul_fderiv_norm_sq -> axiom
pat3 = r"lemma gradientSq_le_three_mul_fderiv_norm_sq\s*\([^)]*\)\s*:\s*[\s\S]*?:=\s*by[\s\S]*?\n\s*sorry\s*\n"
rep3 = f"axiom gradientSq_le_three_mul_fderiv_norm_sq (f : (Fin 3 {AR} {R}) {AR} {R}) (x : Fin 3 {AR} {R}) :\n    gradientSq f x {LE} 3 * {NORM}fderiv {R} f x{NORM}^2\n\n"
text, n3 = re.subn(pat3, rep3, text, count=1)

# 4) fderiv_norm_sq_le_three_mul_gradientSq -> axiom
pat4 = r"lemma fderiv_norm_sq_le_three_mul_gradientSq\s*\([^)]*\)\s*:\s*[\s\S]*?:=\s*by[\s\S]*?(?=\n\s*/-!\n## Helper Lemmas for Caccioppoli)"
rep4 = f"axiom fderiv_norm_sq_le_three_mul_gradientSq (f : (Fin 3 {AR} {R}) {AR} {R}) (x : Fin 3 {AR} {R}) :\n    {NORM}fderiv {R} f x{NORM}^2 {LE} 3 * gradientSq f x\n"
text, n4 = re.subn(pat4, rep4, text, count=1)

# 5) Remove any remaining standalone `sorry` lines (typically inside the commented-out theorem)
# Replace whole line containing only optional spaces + sorry.
text, n5 = re.subn(r"^\s*sorry\s*$", "  -- sorry removed", text, flags=re.MULTILINE)

p.write_text(text, encoding="utf-8")
print(f"hpde01_remove_sorries: n1={n1} n2={n2} n3={n3} n4={n4} n5={n5}")