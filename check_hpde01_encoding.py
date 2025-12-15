from pathlib import Path
p = Path(r"C:\v2_files\lean_proofs\HPDE_01_caccioppoli\HPDE_01_caccioppoli\EllipticCaccioppoli.lean")
s = p.read_text(encoding="utf-8")
print("has_sorry", "sorry" in s)
print("has_mojibake_a", "\u00e2" in s)  # 'Ã¢'
print("has_repl_char", "\ufffd" in s)  # replacement character
# show the axiom line escaped
for line in s.splitlines():
    if line.strip().startswith("axiom gradientSq_le_fderiv_norm_sq"):
        print("axiom_line_escaped", line.encode("unicode_escape").decode("ascii"))
        break