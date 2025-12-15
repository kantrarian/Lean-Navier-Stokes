from pathlib import Path
import re

p = Path(r"C:\v2_files\lean_proofs\LHF_01_commutator\LHF_01_manual.lean")
text = p.read_text(encoding="utf-8")

# add import for MatrixCalculus if missing
imp = "import LHF_01_commutator.MatrixCalculus\n"
if imp not in text:
    m = re.search(r"(^(?:import .*\n)+)", text, flags=re.MULTILINE)
    if not m:
        raise SystemExit("could not locate import block")
    text = text[:m.end(1)] + imp + text[m.end(1):]

# remove the two axioms (rotation_rate, time_deriv)
text, n1 = re.subn(r"^axiom\s+rotation_rate[\s\S]*?\n", "", text, flags=re.MULTILINE, count=1)
text, n2 = re.subn(r"^axiom\s+time_deriv[\s\S]*?\n", "", text, flags=re.MULTILINE, count=1)

# scrub any lingering references in comments only if needed (leave as-is otherwise)

p.write_text(text, encoding="utf-8")
print(f"patched LHF_01_manual: added_import={imp in text}, removed_rotation_rate={n1}, removed_time_deriv={n2}")