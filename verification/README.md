# Verification record and provenance

The Lean proof sources, audit files, toolchain declaration, Lake configuration,
and dependency manifest in this repository are byte-for-byte identical to the
frozen verified sources from October 2, 2026. Repository-facing documentation
and wrapper scripts have been curated separately; this is not a claim that
all repository files have the original snapshot hashes.

## Original local checks

1. [Original complete run](2026-10-02/verification-final.log): build, source
   guard, all-declaration axiom audit, and expanded statements passed
2. [Separate-copy clean project rebuild](2026-10-02/independent-rerun/parent-verification.log):
   the project modules were rebuilt, reusing the pinned dependency cache;
   [source hashes before](2026-10-02/independent-rerun/source-hash-check.log)
   and [after](2026-10-02/independent-rerun/final-source-hash-check.log) agreed

These are two local computational runs, not reviews by independent experts.
“Independent rerun” in the historical folder name means a separate local copy.
Neither run was a from-source rebuild of the entire Lean toolchain and mathlib.
Historical logs are preserved unedited, including their original wording about
no remote publication having occurred at that time.

[Summary](2026-10-02/audit-summary.log) ·
[All axiom reports](2026-10-02/axioms-final.log) ·
[Expanded statements](2026-10-02/statement-audit.log) ·
[Recorded metadata](2026-10-02/verification-metadata.json)

All **245** proved declarations were audited. The three closed conclusion
statements have only `propext`, `Classical.choice`, and `Quot.sound` as axiom
dependencies. No custom axiom or proof placeholder was used. The real-domain
conclusion explicitly includes both infinite nonnegative total weight and
ordinary real nonsummability.

## Integrity

Run the portable integrity check from the repository root:

```sh
python3 scripts/check_integrity.py
```

[proof-SHA256SUMS](proof-SHA256SUMS) covers the unchanged proof and pinned
build inputs. [artifact-SHA256SUMS](artifact-SHA256SUMS) covers the original supplied
paper, now preserved in `paper/original-2026-10-02/`, and the complete frozen archive.
The October 23 editorial revision is separately identified in the submission
fascicle; it does not replace or change the original paper digests. [frozen-SHA256SUMS](frozen-SHA256SUMS) is
the original manifest for the snapshot layout, kept as a provenance record;
it is not a manifest for the curated repository layout.

The complete frozen source-and-logs archive is
[erdos143-lean-complete-verified-20261002.zip](erdos143-lean-complete-verified-20261002.zip),
SHA-256:

```text
d4a8477e5122ad7f66584483b84a93b14af38b3a412c8b9378617b2c2137fec6
```

It contains the exact original scripts and documentation as well as both
verification records. This small archive is retained to make the paper's
specific provenance reference inspectable. It contains no `.lake` cache or
Lean toolchain. The source-only tarball identified in historical metadata is
not needed for reproduction; its contents are represented by the frozen ZIP.

## Fresh verification

```sh
bash scripts/bootstrap.sh
bash scripts/verify.sh
```

These commands write new results to ignored `logs/`. They do not replace the
historical records. The Lean version and all dependency revisions remain
pinned. Successful kernel checking establishes the formal statements from the
listed foundations; it does not establish priority, external acceptance, or
that every prose explanation has been independently reviewed.

## October 23, 2026 local verification

[Fresh verification records](2026-10-23/) record a successful 3,333-job
build, the complete 245-declaration axiom audit, the expanded statement
audit, and the additional manuscript-specific checks. The pinned nine
dependency revisions were checked against the lockfile, with their tracked
sources unchanged. The original proof source digests still match.

The additional check is
`submission/blms-2026-10-23/ManuscriptAudit.lean`; it explicitly checks the
strong conclusion, the same recursive witness and its prefix mass bound.
These are new local computational checks, not independent expert review.

The supplementary audit now also checks `Erdos143.manuscript_full_statement`,
a single existential statement with explicit infinitude and the same finite
prefixes. This additional corollary was compiled separately on October 23;
its axiom report is in `2026-10-23/manuscript-audit.log`. It is not included
in the count of 245 declarations of the unchanged frozen project.
