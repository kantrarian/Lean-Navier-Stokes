from pathlib import Path

p = Path(r"C:\v2_files\lean_proofs\HPDE_01_caccioppoli\HPDE_01_caccioppoli\EllipticCaccioppoli.lean")
s = p.read_text(encoding="utf-8")
# replace Pi.single i 1 with Pi.single i (1 : â„)
s = s.replace("Pi.single i 1", "Pi.single i (1 : \u211d)")
p.write_text(s, encoding="utf-8")
print("fixed Pi.single i 1")