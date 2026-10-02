# The paper

**A rational counterexample to the reciprocal-logarithmic assertion in Erdős
problem 143**

Mattia Apicella · October 2, 2026

- [Read the reviewed 15-page PDF](erdos143-candidate.pdf)
- [Edit the complete LaTeX source](erdos143-candidate.tex)
- [Inspect the companion formalization](../Erdos143/RealConclusion.lean)

Both files are byte-for-byte copies of the final supplied English paper.
The source is self-contained: bibliography and three TikZ figures are embedded,
with no separate images or bibliography database required.

From the repository root:

```sh
bash scripts/build-paper.sh
```

This runs `pdflatex` twice and writes the rebuilt PDF and logs to `paper/build/`,
leaving the reviewed PDF unchanged. Use TeX Live or MiKTeX with `amsart`,
`amsmath`, `amssymb`, `mathtools`, `microtype`, `geometry`, `hyperref`, TikZ,
and `placeins`. The font is Computer Modern. A source rebuild can differ in
PDF metadata and need not have the same binary hash.

Typesetting does not execute Lean. Run the formal checks separately as described
in the [main README](../README.md). References in the paper to the companion
frozen archive resolve to [the archive preserved here](../verification/erdos143-lean-complete-verified-20261002.zip).
The paper's two explanatory Markdown notes now live in [`docs/`](../docs/README.md).

Independent expert review is pending; the local formal checks are described
precisely in the paper and in the [verification record](../verification/README.md).
