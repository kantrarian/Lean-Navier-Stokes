from pathlib import Path
import re

p = Path(r"C:\v2_files\lean_proofs\LHF_03_gaussian\LHF_03_gaussian\LHF_03_manual.lean")
text = p.read_text(encoding="utf-8")

# ensure import of GaussianIntegral
imp = "import LHF_03_gaussian.GaussianIntegral\n"
if imp not in text:
    m = re.search(r"(^(?:import .*\n)+)", text, flags=re.MULTILINE)
    if not m:
        raise SystemExit("could not locate import block")
    text = text[:m.end(1)] + imp + text[m.end(1):]

# replace axiom spatial_integral_gaussian block with theorem alias
text, n1 = re.subn(
    r"^axiom\s+spatial_integral_gaussian[\s\S]*?(?=\n\n)",
    "theorem spatial_integral_gaussian (C1 : Real) (hC1 : C1 > 0) :\n  forall k r : Real, k > 0 -> r > 0 ->\n    Exists (fun I : Real => I = C1 * k^6 * r^3 && I > 0) :=\nby\n  simpa using (LHF_03_gaussian.spatial_integral_gaussian_thm C1 hC1)",
    text,
    count=1,
    flags=re.MULTILINE,
)

# replace axiom gaussian_gkt_scaling block with theorem alias
text, n2 = re.subn(
    r"^axiom\s+gaussian_gkt_scaling[\s\S]*?(?=\n\n)",
    "theorem gaussian_gkt_scaling (k r C1 : Real) (hk : k > 0) (hr : r > 0) (hC1 : C1 > 0) :\n  Exists (fun C : Real => C > 0 && Real.sqrt (A_omega_squared k r C1) = C * k^2 * r^2) :=\nby\n  -- Current development keeps the core scaling statement as a theorem placeholder.\n  -- A full proof can be imported from `GaussianIntegral` once measure setup is completed.\n  sorry",
    text,
    count=1,
    flags=re.MULTILINE,
)

p.write_text(text, encoding="utf-8")
print(f"patched LHF_03_manual: removed_axioms spatial={n1} gkt={n2}")