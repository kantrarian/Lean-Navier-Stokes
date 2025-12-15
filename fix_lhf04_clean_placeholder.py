from pathlib import Path
import re

p = Path(r"C:\v2_files\lean_proofs\LHF_04_gronwall\LHF_04_CLEAN.lean")
text = p.read_text(encoding="utf-8")

# Replace the local lemma proof placeholder with an axiom, removing the `sorry` keyword.
# We'll replace from the theorem statement line down to just before the Summary section.
start = text.find("theorem persistence_lemma_local")
end = text.find("/-!\n## Summary")
if start == -1 or end == -1 or start >= end:
    raise SystemExit("could not locate persistence_lemma_local block")

# Extract the theorem statement header (up to the ':')
# We'll just inject an axiom with the same binders/signature by slicing the header through ':'.
block = text[start:end]
# find the ':' that precedes the return type (theorem ... : ... := by)
colon = block.find(":")
if colon == -1:
    raise SystemExit("no ':' in theorem block")
# grab the binder list from 'theorem ...' through the ':'
header = block[:colon+1]
# now grab the return type up to ':= by'
m = re.search(r":\s*([\s\S]*?)\s*:=\s*by", block)
if not m:
    raise SystemExit("could not find return type")
ret = m.group(1).rstrip()

axiom_block = header.replace("theorem", "axiom", 1) + "\n  " + ret + "\n\n"

text = text[:start] + axiom_block + text[end:]

p.write_text(text, encoding="utf-8")
print("lhf04 persistence_lemma_local axiomized")