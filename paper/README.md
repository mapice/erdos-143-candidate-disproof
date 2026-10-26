# The paper

**A rational counterexample to the reciprocal-logarithmic assertion in Erdős problem 143**

Mattia Apicella · October 2, 2026; revised October 26, 2026.

- [Current 12-page PDF](erdos143-candidate.pdf)
- [Corresponding standalone LaTeX source](erdos143-candidate.tex)
- [Revision and Lean correspondence](../docs/Revision-correspondence-2026-10-25.md)
- [Selberg–Delange assessment](../docs/selberg-delange-review-2026-10-25.md)
- [October 23 submitted manuscript](submitted-2026-10-23/)
- [October 2 original manuscript](original-2026-10-02/)

The current version brings the complete finite-extension proposition forward,
explains its immediate iteration, and then proves it by a finite induction
with explicit hypotheses. The two primes are now denoted `p` and `q`;
composite numerator and denominator abbreviations have been removed.
The analytic section uses a short logarithmic Euler-product estimate.

The main theorem is identical to the October 23 statement. All 55 original
Lean modules remain unchanged. Six additional modules now formalize the
revised logarithmic argument as a separate closed proof of the same
periodic-selection interface. See the [October 26 correspondence](../docs/Logarithmic-correspondence-2026-10-26.md).
The dated source archives retain the paper versions that they originally
accompanied. The new version is deposited at
https://doi.org/10.5281/zenodo.23676536.

From the repository root:

```sh
bash scripts/build-paper.sh
```

This runs `pdflatex` twice and writes the rebuilt PDF and logs to `paper/build/`.
The reviewed PDF is refreshed explicitly after inspection. The source requires
`amsart`, `fontenc`, `amsmath`, `amssymb`, `mathtools`, `microtype`, `needspace`
and `hyperref`; no external figures or bibliography database are required.
A rebuild can differ in PDF metadata and binary hash.

Typesetting does not execute Lean. Reproduction commands and the exact scope
of the recorded formal checks are in the [main README](../README.md) and
[verification record](../verification/README.md).
