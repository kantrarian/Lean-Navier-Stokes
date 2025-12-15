from pathlib import Path

p = Path(r"C:\v2_files\lean_proofs\HPDE_01_caccioppoli\HPDE_01_caccioppoli\EllipticCaccioppoli.lean")
s = p.read_text(encoding="utf-8")
old = "have h := norm_le_pi_norm (Pi.single i (1 : \u211d)) i"
new = "have h := norm_le_pi_norm (Pi.single i (1 : \u211d) : Fin 3 \u2192 \u211d) i"
if old not in s:
    raise SystemExit("target line not found")
s = s.replace(old, new, 1)
p.write_text(s, encoding="utf-8")
print("fixed norm_le_pi_norm annotation")