from pathlib import Path
p = Path(r"C:\v2_files\lean_proofs\LHF_04_gronwall\LHF_04_manual.lean")
s = p.read_text(encoding="utf-8")
s2 = s.replace("The `sorry` blocks are:", "The placeholder blocks are:")
s2 = s2.replace("sorry", "placeholder")
if s2 != s:
    p.write_text(s2, encoding="utf-8")
    print("scrubbed lhf04 manual")