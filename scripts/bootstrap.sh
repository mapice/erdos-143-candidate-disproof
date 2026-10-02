#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LEAN_VERSION=4.24.0
LEAN_SHA256=b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec
mkdir -p tooling logs
if [[ -x "tooling/lean-${LEAN_VERSION}-linux/bin/lean" ]]; then
  export PATH="$PWD/tooling/lean-${LEAN_VERSION}-linux/bin:$PATH"
elif ! command -v lake >/dev/null 2>&1; then
  if [[ "$(uname -s)" != Linux || "$(uname -m)" != x86_64 ]]; then
    printf 'Install Lean 4.24.0 via https://github.com/leanprover/elan for your platform, then rerun this script.\n' >&2
    exit 1
  fi
  archive="tooling/lean-${LEAN_VERSION}-linux.tar.zst"
  curl --fail --location --retry 3 \
    "https://github.com/leanprover/lean4/releases/download/v${LEAN_VERSION}/lean-${LEAN_VERSION}-linux.tar.zst" \
    -o "$archive"
  python3 - "$archive" "$LEAN_SHA256" <<'PY'
import hashlib, pathlib, sys
p = pathlib.Path(sys.argv[1])
if hashlib.sha256(p.read_bytes()).hexdigest() != sys.argv[2]:
    raise SystemExit('Lean release checksum mismatch')
print('Official Lean release SHA-256 verified')
PY
  tar --zstd -xf "$archive" -C tooling
  export PATH="$PWD/tooling/lean-${LEAN_VERSION}-linux/bin:$PATH"
fi
lean --version | tee logs/bootstrap-toolchain.log
grep -q 'Lean (version 4\.24\.0,' logs/bootstrap-toolchain.log || {
  printf 'Expected Lean 4.24.0. Check lean-toolchain and your PATH.\n' >&2; exit 1;
}
export XDG_CACHE_HOME="$PWD/tooling/cache"
python3 scripts/check_integrity.py
# Lake materializes the revisions already recorded in lake-manifest.json.
# Do not run lake update: it is unnecessary for the pinned reproduction.
imports=()
while IFS= read -r module; do imports+=("$module"); done < <(
  grep -h '^import Mathlib\.' Erdos143/*.lean | awk '{print $2}' | sort -u
)
lake exe cache get "${imports[@]}" 2>&1 | tee logs/bootstrap-cache.log
python3 scripts/check_integrity.py
printf '\nPinned toolchain and dependencies are ready. Run bash scripts/verify.sh.\n'
