#!/usr/bin/env python3
"""Generate a complete #print axioms audit of the project's public proofs."""
import pathlib
import re
import sys
root = pathlib.Path(__file__).resolve().parent.parent
names = []
for path in sorted((root / "Erdos143").glob("*.lean")):
    source = path.read_text()
    names.extend(re.findall(r"^(?:@\[[^\n]*\]\s*)?(?:lemma|theorem)\s+([\w'.]+)", source, re.M))
if len(names) != len(set(names)):
    raise SystemExit("Duplicate proved declaration names")
text = "import Erdos143\n\n"
text += "\n".join("#print axioms Erdos143." + name for name in names)
text += "\n\n#print Erdos143.MainConclusion\n#print Erdos143.StrongConclusion\n#check Erdos143.mainConclusion_proved\n#check Erdos143.strongConclusion_proved\n#check Erdos143.realConclusion_proved\n"
if "--check" in sys.argv:
    if (root / "AxiomAudit.lean").read_text() != text:
        raise SystemExit("AxiomAudit.lean is stale; run python3 scripts/generate_audit.py")
    print(f"Audit matches all {len(names)} proved declarations")
else:
    (root / "AxiomAudit.lean").write_text(text)
    print(f"Audit generated for {len(names)} proved declarations")
