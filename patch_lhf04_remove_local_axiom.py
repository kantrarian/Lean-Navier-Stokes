from pathlib import Path
import re

paths = [
    Path(r"C:\v2_files\lean_proofs\LHF_04_gronwall\LHF_04_CLEAN.lean"),
    Path(r"C:\v2_files\lean_proofs\LHF_04_gronwall\LHF_04_gronwall\LHF_04_CLEAN.lean"),
]

for p in paths:
    if not p.exists():
        continue
    text = p.read_text(encoding="utf-8")
    # Remove the axiom declaration line (and any following type lines until blank line)
    text2, n = re.subn(r"^axiom\s+persistence_lemma_local\b[\s\S]*?\n\n",
                       "-- persistence_lemma_local removed in axiom-elimination sprint\n\n",
                       text,
                       count=1,
                       flags=re.MULTILINE)
    if n != 1:
        raise SystemExit(f"failed to remove axiom in {p}, matches={n}")
    p.write_text(text2, encoding="utf-8")
    print("removed axiom from", p)