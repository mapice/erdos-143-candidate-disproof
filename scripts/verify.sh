#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
if [[ -x tooling/lean-4.24.0-linux/bin/lean ]]; then
  export PATH="$PWD/tooling/lean-4.24.0-linux/bin:$PATH"
fi
export XDG_CACHE_HOME="$PWD/tooling/cache"
mkdir -p logs
python3 scripts/check_integrity.py | tee logs/integrity.log
python3 scripts/check_sources.py | tee logs/source-check.log
python3 scripts/generate_audit.py --check
lean --version | tee logs/toolchain.log
grep -q 'Lean (version 4\.24\.0,' logs/toolchain.log || {
  printf 'Expected Lean 4.24.0. Run scripts/bootstrap.sh first.\n' >&2; exit 1;
}
lake build 2>&1 | tee logs/build-final.log
lake env lean -DwarningAsError=true AxiomAudit.lean 2>&1 | tee logs/axioms-final.log
python3 scripts/check_axioms.py logs/axioms-final.log | tee logs/audit-summary.log
lake env lean -DwarningAsError=true StatementAudit.lean 2>&1 | tee logs/statement-audit.log
python3 scripts/check_integrity.py
printf '\nVerification passed: build, 245-declaration axiom audit, and statement audit.\n'
