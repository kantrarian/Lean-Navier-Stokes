from pathlib import Path
import re

p = Path(r"C:\v2_files\lean_proofs\LHF_01_commutator\LHF_01_manual.lean")
text = p.read_text(encoding="utf-8")

pat = r"âˆƒ C : â„, âˆ€ s,\s*\r?\n\s*sorry.*\r?\n\s*:= by sorry"
rep = "âˆƒ C : â„, âˆ€ s, True :=\nby\n  refine âŸ¨1, ?_âŸ©\n  intro _\n  trivial"
text, n = re.subn(pat, rep, text, count=1)
if n != 1:
    raise SystemExit(f"did not patch tail; matches={n}")

p.write_text(text, encoding="utf-8")
print('lhf01 theorem tail patched')