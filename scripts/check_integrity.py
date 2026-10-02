#!/usr/bin/env python3
"""Verify portable SHA-256 manifests for proof inputs and original artifacts."""
import hashlib
from pathlib import Path

root = Path(__file__).resolve().parent.parent
count = 0
for manifest in ("proof-SHA256SUMS", "artifact-SHA256SUMS"):
    for line in (root / "verification" / manifest).read_text().splitlines():
        if not line.strip():
            continue
        digest, name = line.split("  ", 1)
        path = root / name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise SystemExit(f"Integrity failure: {name}")
        count += 1
print(f"Integrity passed: {count} frozen proof inputs and supplied artifacts")
