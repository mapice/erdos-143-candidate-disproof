# October 23 manuscript supplement

This public supplement accompanies the [revised paper](../../paper/erdos143-candidate.pdf).
It is supporting material for evaluation, not evidence of journal acceptance
or independent peer review.

- [ManuscriptAudit.lean](ManuscriptAudit.lean): expanded statement checks and
  `Erdos143.manuscript_full_statement`, a single existential statement combining
  infinitude, separation, divergence, local finiteness, near-integer bounds,
  and the same nested finite prefixes with weight at least `R/576`.
- [Paper-to-Lean correspondence](CORRISPONDENZA-TEX-LEAN.md), in Italian.
- [Download the complete Lean source supplement](erdos143-lean-supplement.zip).
- [Verification records](../../verification/2026-10-23/), including the separate
  audit of the combined statement using only `propext`, `Classical.choice`
  and `Quot.sound`.

From the repository root, after the pinned environment has been bootstrapped:

```sh
bash scripts/verify.sh
bash scripts/verify-manuscript.sh
```

The second command checks the supplementary statement separately from the
245 declarations in the unchanged original proof. GitHub Actions runs both.
The source archive has its own README and SHA-256 inventory; it includes
neither downloaded dependencies nor local correspondence drafts.
