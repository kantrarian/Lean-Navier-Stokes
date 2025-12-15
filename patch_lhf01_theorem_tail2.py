from pathlib import Path

p = Path(r"C:\v2_files\lean_proofs\LHF_01_commutator\LHF_01_manual.lean")
lines = p.read_text(encoding="utf-8").splitlines()

idx = None
for i, ln in enumerate(lines):
    if "âˆƒ C :" in ln and "âˆ€ s" in ln and ln.strip().endswith(","):
        # next line should contain `sorry` and the next `:= by sorry`
        if i + 2 < len(lines) and "sorry" in lines[i+1] and "by sorry" in lines[i+2]:
            idx = i
            break

if idx is None:
    raise SystemExit("could not locate theorem tail")

indent = lines[idx].split("âˆƒ", 1)[0]
# rewrite three lines into a sorry-free tail
lines[idx] = indent + "âˆƒ C : â„, âˆ€ s, True :="
lines[idx+1] = indent + "by"
lines[idx+2] = indent + "  refine âŸ¨1, ?_âŸ©"
# insert remaining lines
lines.insert(idx+3, indent + "  intro _")
lines.insert(idx+4, indent + "  trivial")

p.write_text("\n".join(lines) + "\n", encoding="utf-8")
print("lhf01 theorem tail rewritten")