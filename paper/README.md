# The paper

**A rational counterexample to the reciprocal-logarithmic assertion in Erdős problem 143**

Mattia Apicella · October 2, 2026; revised October 23, 2026.

- [Current 16-page PDF](erdos143-candidate.pdf)
- [Corresponding standalone LaTeX source](erdos143-candidate.tex)
- [Companion formal statement](../Erdos143/RealConclusion.lean)
- [Public proof supplement and combined statement](../submission/blms-2026-10-23/README.md)

The October 23 revision is prepared for initial consideration by the Bulletin
of the London Mathematical Society. It uses the standard `amsart` layout,
Computer Modern, a self-contained abstract and a motivating introduction,
and includes an AI Declaration and a separate mathematical-software statement.
The mathematical construction and frozen Lean sources are unchanged.
The three explanatory figures from the original version have been removed
from this research submission; the proof retains their mathematical content.

The original October 2 source and PDF are preserved byte for byte in
[original-2026-10-02/](original-2026-10-02/). Their original digests remain
checked by `verification/artifact-SHA256SUMS`; the paths in that manifest
now identify the preserved originals.

From the repository root:

```sh
bash scripts/build-paper.sh
```

This runs `pdflatex` twice and writes the rebuilt PDF and logs to `paper/build/`.
The reviewed PDF at the path above is refreshed explicitly after inspection.
The source requires `amsart`, `fontenc`, `amsmath`, `amssymb`, `mathtools`,
`microtype`, `needspace` and `hyperref`; no external figures, bibliography database,
custom journal class or shell escape are required.
A source rebuild can differ in PDF metadata and binary hash.

Typesetting does not execute Lean. Run the formal checks separately as
described in the [main README](../README.md). Historical and fresh local
checks are distinguished in the [verification record](../verification/README.md).
Independent expert review is pending; no journal submission or acceptance
is implied by this preparation.
