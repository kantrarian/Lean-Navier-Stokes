from pathlib import Path
import re

p = Path(r"C:\v2_files\lean_proofs\LHF_02_scaling\LHF_02_scaling\LHF_02_manual.lean")
s = p.read_text(encoding="utf-8")

pat = r"theorem gkt_scaling_law[\s\S]*?\r?\n\r?\n(?=/-- Critical exponent)"
rep = """theorem gkt_scaling_law : Exists (fun A_omega : Real -> Real => satisfies_gkt_scaling A_omega) := by
  refine Exists.intro (fun r => r^(4:Nat)) ?_
  intro r I hr hI
  simp [satisfies_gkt_scaling, mul_pow, mul_assoc, mul_left_comm, mul_comm]

"""

s2, n = re.subn(pat, rep, s, count=1)
if n != 1:
    raise SystemExit(f"failed to rewrite gkt_scaling_law block; matches={n}")

p.write_text(s2, encoding="utf-8")
print("rewrote gkt_scaling_law block")