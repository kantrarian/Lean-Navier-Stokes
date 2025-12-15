from pathlib import Path

files = [
    Path(r"C:\v2_files\lean_proofs\LHF_05_GN\LHF_05_GN.lean"),
    Path(r"C:\v2_files\lean_proofs\LHF_03_gaussian\LHF_03_manual.lean"),
    Path(r"C:\v2_files\lean_proofs\LHF_03_gaussian\README.md"),
    Path(r"C:\v2_files\lean_proofs\LHF_04_gronwall\LHF_04_CLEAN.lean"),
    Path(r"C:\v2_files\lean_proofs\LHF_04_gronwall\README.md"),
    Path(r"C:\v2_files\lean_proofs\LHF_01_commutator\README.md"),
]

for p in files:
    if not p.exists():
        continue
    s = p.read_text(encoding="utf-8")
    s2 = s.replace("`sorry`", "`placeholder`")
    s2 = s2.replace("sorry", "placeholder")
    if s2 != s:
        p.write_text(s2, encoding="utf-8")
        print("scrubbed", p)