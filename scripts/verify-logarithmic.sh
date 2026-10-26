#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
if [[ -x tooling/lean-4.24.0-linux/bin/lake ]]; then
  export PATH="$PWD/tooling/lean-4.24.0-linux/bin:$PATH"
fi
export XDG_CACHE_HOME="$PWD/tooling/cache"
mkdir -p logs
lake env lean -DwarningAsError=true LogarithmicAudit.lean 2>&1 | tee logs/logarithmic-audit.log
python3 - <<'PY'
from pathlib import Path
import re
text = Path('logs/logarithmic-audit.log').read_text()
if 'Logarithmic dependency audit passed:' not in text:
    raise SystemExit('Missing logarithmic dependency check')
reports = re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text, re.M)
expected = {
    'Erdos143.generatingValue_logarithmic_identity',
    'Erdos143.prime_logarithmic_remainder_summable_and_norm_le',
    'Erdos143.Logarithmic.remainderBound_proved',
    'Erdos143.Logarithmic.periodicPrimitiveSelection_logarithmic_proved',
}
if len(reports) != len(expected) or {name for name, _ in reports} != expected:
    raise SystemExit('Missing or duplicate logarithmic axiom report')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, axioms in reports:
    if not {a.strip() for a in axioms.split(',') if a.strip()} <= allowed:
        raise SystemExit(f'Unexpected axiom: {name}')
print('Logarithmic verification passed: closed selection theorem, standard foundations, and separate analytic dependency path.')
PY
