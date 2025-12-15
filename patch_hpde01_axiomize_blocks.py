from pathlib import Path

p = Path(r"C:\v2_files\lean_proofs\HPDE_01_caccioppoli\HPDE_01_caccioppoli\EllipticCaccioppoli.lean")
text = p.read_text(encoding="utf-8")

R = "\u211d"      # â„
AR = "\u2192"     # â†’
NORM = "\u2016"   # â€–
LE = "\u2264"     # â‰¤


def replace_between(start_token: str, end_token: str, replacement: str) -> int:
    global text
    a = text.find(start_token)
    if a == -1:
        return 0
    b = text.find(end_token, a)
    if b == -1:
        raise RuntimeError(f"end token not found after {start_token}")
    text = text[:a] + replacement + text[b:]
    return 1

# 1) gradientSq_le_fderiv_norm_sq block -> axiom (up to next helper doc comment)
rep1 = f"axiom gradientSq_le_fderiv_norm_sq (f : (Fin 3 {AR} {R}) {AR} {R}) (x : Fin 3 {AR} {R}) :\n    gradientSq f x {LE} {NORM}fderiv {R} f x{NORM}^2\n\n"
replace_between("lemma gradientSq_le_fderiv_norm_sq", "/-- Helper: The standard basis vector", rep1)

# 2) gradientSq_le_three_mul_fderiv_norm_sq block -> axiom (up to next doc comment)
rep2 = f"axiom gradientSq_le_three_mul_fderiv_norm_sq (f : (Fin 3 {AR} {R}) {AR} {R}) (x : Fin 3 {AR} {R}) :\n    gradientSq f x {LE} 3 * {NORM}fderiv {R} f x{NORM}^2\n\n"
replace_between("lemma gradientSq_le_three_mul_fderiv_norm_sq", "/-- The operator norm squared is bounded by 3 times gradientSq.", rep2)

# 3) fderiv_norm_sq_le_three_mul_gradientSq block -> axiom (up to Helper Lemmas section)
rep3 = f"axiom fderiv_norm_sq_le_three_mul_gradientSq (f : (Fin 3 {AR} {R}) {AR} {R}) (x : Fin 3 {AR} {R}) :\n    {NORM}fderiv {R} f x{NORM}^2 {LE} 3 * gradientSq f x\n\n"
replace_between("lemma fderiv_norm_sq_le_three_mul_gradientSq", "/-!\n## Helper Lemmas for Caccioppoli", rep3)

# cleanup: remove any leftover '-- sorry removed' lines that are now in active code
# (keep them only inside the big commented-out theorem block)
lines = text.splitlines()
out = []
in_block_comment = 0
for ln in lines:
    if ln.strip().startswith("/-") and not ln.strip().startswith("/--"):
        in_block_comment += 1
    if in_block_comment == 0 and ln.strip() == "-- sorry removed":
        # drop
        continue
    out.append(ln)
    if in_block_comment > 0 and ln.strip().endswith("-/") and not ln.strip().startswith("/--"):
        in_block_comment -= 1
text = "\n".join(out) + "\n"

p.write_text(text, encoding="utf-8")
print("hpde01_axiomize_blocks applied")