#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
if [[ -x tooling/lean-4.24.0-linux/bin/lake ]]; then
  export PATH="$PWD/tooling/lean-4.24.0-linux/bin:$PATH"
fi
export XDG_CACHE_HOME="$PWD/tooling/cache"
mkdir -p logs
lake env lean -DwarningAsError=true submission/blms-2026-10-23/ManuscriptAudit.lean   2>&1 | tee logs/manuscript-audit.log
python3 - <<'AUDIT'
from pathlib import Path
import re
text = Path("logs/manuscript-audit.log").read_text()
reports = re.findall(r"'([^']+)' depends on axioms: \[([^]]+)\]", text)
expected = {
    "Erdos143.mainConclusion_proved", "Erdos143.strongConclusion_proved",
    "Erdos143.realConclusion_proved", "Erdos143.manuscript_full_statement",
}
if len(reports) != len(expected) or {name for name, _ in reports} != expected:
    raise SystemExit("Missing or duplicate supplementary axiom report")
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name, axioms in reports:
    if {axiom.strip() for axiom in axioms.split(",")} != allowed:
        raise SystemExit(f"Unexpected axiom dependencies: {name}")
print("Supplementary verification passed: combined manuscript statement and standard axiom dependencies.")
AUDIT
