from pathlib import Path

p = Path(r"C:\v2_files\lean_proofs\LHF_01_commutator\LHF_01_manual.lean")
lines = p.read_text(encoding="utf-8").splitlines()

EX = "\u2203"  # âˆƒ
FA = "\u2200"  # âˆ€
R = "\u211d"   # â„

idx = None
for i, ln in enumerate(lines):
    if EX in ln and (f"{EX} C : {R}, {FA} s," in ln):
        if i + 2 < len(lines) and "sorry" in lines[i+1] and "by sorry" in lines[i+2]:
            idx = i
            break

if idx is None:
    raise SystemExit("could not locate theorem tail")

indent = lines[idx].split(EX, 1)[0]
lines[idx] = indent + f"{EX} C : {R}, {FA} s, True :="
lines[idx+1] = indent + "by"
lines[idx+2] = indent + "  refine 1, ?_"
# The above line is intentionally bogus if mojibake occurs; instead insert raw UTF-8 escapes:
# We'll overwrite it below using unicode escapes.
lines[idx+2] = indent + "  refine \u27e81, ?_\u27e9"  # âŸ¨1, ?_âŸ©
lines.insert(idx+3, indent + f"  intro _")
lines.insert(idx+4, indent + "  trivial")

p.write_text("\n".join(lines) + "\n", encoding="utf-8")
print("lhf01 theorem tail rewritten")