from pathlib import Path
import re

p = Path(r"C:\v2_files\lean_proofs\LHF_02_scaling\LHF_02_scaling\LHF_02_manual.lean")
s = p.read_text(encoding="utf-8")

# Drop the `ring` lines that follow a `simp ...` in the two theorems.
s, n_ring1 = re.subn(r"(simp \[satisfies_gkt_scaling, mul_pow, mul_assoc, mul_left_comm, mul_comm\]\r?\n)\s*ring\r?\n",
                     r"\1",
                     s,
                     count=2)

# Replace mojibake refine line with ASCII-safe Exists.intro
s, n_ref = re.subn(r"\s*refine .*\?_.*\r?\n",
                   "  refine Exists.intro (fun r => r^(4:Nat)) ?_\n",
                   s,
                   count=1)

p.write_text(s, encoding="utf-8")
print(f"patched LHF_02_manual: removed_ring={n_ring1}, fixed_refine={n_ref}")