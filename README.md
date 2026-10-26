# A rational counterexample for Erdős problem 143

**Mattia Apicella · October 2, 2026; revised October 26, 2026**

A candidate disproof of the **reciprocal-logarithmic convergence assertion** in
[Erdős problem 143](https://www.erdosproblems.com/143), with a complete Lean 4
formalization and a self-contained mathematical paper.

[Read the paper (PDF)](paper/erdos143-candidate.pdf) ·
[Read the LaTeX source](paper/erdos143-candidate.tex) ·
[Inspect the exact formal statement](Erdos143/RealConclusion.lean) ·
[Verification evidence](verification/README.md)

> **Status.** The closed existence theorems have passed local Lean kernel
> checks and an axiom audit of all 319 proved declarations. Independent expert
> review of the formulation, its correspondence to Erdős's question, and the
> exposition is still pending. No priority, peer review, or external acceptance
> is claimed. The repository name retains “candidate” for this reason.

## The statement

There exists a countable set of rational numbers $A\subset[2,\infty)$ such that

$$ |ka-b|\geq 1 \qquad(a,b\in A,\ a\ne b,\ k\in\mathbb Z_{\geq1}), $$

but

$$ \sum_{a\in A}\frac{1}{a\log a}=\infty. $$

Here $\log$ is the natural logarithm and the separation condition quantifies
over **all ordered pairs** of distinct elements and **every positive integer**
multiplier. The sum is the supremum of finite subsums of nonnegative terms.
The real-domain theorem explicitly proves both an `ENNReal` sum equal to `⊤`
and ordinary real `¬ Summable`; it does not infer divergence from the
conventional value of a nonsummable real `tsum`.

The stronger conclusion also gives local finiteness and, for every $a\in A$,
an integer $m\geq2$ with $0<a-m\leq1/(2m^{12})$.
This concerns the reciprocal-logarithmic assertion specifically; it does not
contradict the accompanying logarithmic-density result discussed in the paper.

## The idea in a minute

1. **Find heavy primitive labels.** Euler products and Dirichlet characters
   give an Abel-average lower bound in every residue class. In any fixed
   periodic set of density greater than $2/3$, this selects arbitrarily distant
   finite primitive sets with weight greater than $1/6$.
2. **Turn labels into separated rational blocks.** Each block receives a
   private prime and a small positive displacement from integer grid points.
   A closed residue filter prevents new points from approaching any integer
   multiple of an earlier point; the other ordered direction is checked too.
3. **Reset the grid and repeat.** A product grid handles the entire old finite
   configuration at the start of each round. The finite private-prime budget
   keeps the forbidden density small. Every round adds weight at least $1/576$.
4. **Take the nested union.** Every ordered pair already appears at a finite
   stage, so separation survives. The uniform round gain forces infinite
   weight. An injective rational-to-real transfer gives the displayed statement.

The argument uses no independence assumption for the periodic exclusions and
no assertion that every sufficiently high individual prime-factor-count layer
has large weight. See the [analytic guide](docs/Abel-periodic-proof.md) and
[construction guide](docs/Construction-correspondence.md).

## Reproduce the formal check

The environment is pinned, including transitive dependencies:

- Lean **4.24.0** (`leanprover/lean4:v4.24.0`)
- mathlib **`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`**
- [Lake configuration](lakefile.toml), [dependency lockfile](lake-manifest.json)

Clone this repository, then run from its root:

```sh
git clone https://github.com/mapice/erdos-143-candidate-disproof.git
cd erdos-143-candidate-disproof
bash scripts/bootstrap.sh
bash scripts/verify.sh
bash scripts/verify-manuscript.sh
```

This repository is public. On Linux x86_64, when Lake is not already available,
the bootstrap downloads the official Lean release and checks its pinned SHA-256.
It requires Bash, Python 3, Git, curl, tar, zstd, and several GB of free disk.
On other platforms, install Lean with [elan](https://github.com/leanprover/elan),
then run the same scripts with `lean` and `lake` on `PATH`; `lean-toolchain`
selects the required version. Internet access is needed to fetch dependencies
and the official mathlib cache. Subsequent checks can reuse them.

Verification checks source integrity and proof escapes, builds with warnings
as errors, checks that the complete declaration audit is current, runs
`#print axioms`, and compiles the expanded statement audit. Fresh logs go to
`logs/`, separate from the committed historical evidence. Success ends with
`Verification passed: build, complete axiom audit, statement audit, and logarithmic-proof audit.`

The key closed theorems, with **no additional analytic or construction
hypotheses**, are:

| Declaration | What it proves | Source |
| --- | --- | --- |
| `Erdos143.mainConclusion_proved` | Complete rational-set existence theorem | [Main.lean](Erdos143/Main.lean) |
| `Erdos143.strongConclusion_proved` | Adds local finiteness and near-integer bounds | [Main.lean](Erdos143/Main.lean) |
| `Erdos143.realConclusion_proved` | Explicit real set, rationality, all quantifiers, divergence and nonsummability | [RealConclusion.lean](Erdos143/RealConclusion.lean) |

Each conclusion depends only on `propext`, `Classical.choice`, and `Quot.sound`,
the standard foundations used here by Lean/mathlib. The project audit rejects
any other axiom and checks all 319 lemmas and theorems. See
[AxiomAudit.lean](AxiomAudit.lean) and [StatementAudit.lean](StatementAudit.lean).
The additional `verify-manuscript.sh` command compiles and audits
`Erdos143.manuscript_full_statement` separately from those 245 declarations.
The source guard is an additional check, not a replacement for kernel checking.

[CI](.github/workflows/verify.yml) runs the same scripts for public-repository
pushes and pull requests. Its job is deliberately skipped while the repository
is private, avoiding private-repository runner usage. Local verification does
not require GitHub Actions or changes to account settings.

## Current manuscript revision

The October 26 manuscript retains the explicit finite extension and the simpler
`p`, `q` notation. Six new modules formalize the shorter logarithmic analytic
argument, including the absolutely convergent double Euler series, the uniform
remainder bound, character limits, all residue classes and primitive selection.
The closed theorem
`Erdos143.Logarithmic.periodicPrimitiveSelection_logarithmic_proved`
has exactly the original `PeriodicPrimitiveSelection` type. The dependency audit
checks that it uses the logarithmic argument and does not invoke the old
Euler-factor comparisons. Both analytic proofs are retained; the original
55 proof modules and the construction are unchanged.

[October 26 logarithmic correspondence](docs/Logarithmic-correspondence-2026-10-26.md)
records the equation-to-theorem mapping and the fresh verification scope.

The [revision correspondence](docs/Revision-correspondence-2026-10-25.md)
explains the notation and proof interfaces. A [technical note](docs/selberg-delange-review-2026-10-25.md)
checks an alternative Selberg–Delange derivation and explains why the shorter
elementary argument is used in the manuscript.

The [October 23 proof supplement](submission/blms-2026-10-23/README.md)
remains a dated archive of the unchanged formal proof and that earlier paper.
The exact October 23 manuscript is preserved in `paper/submitted-2026-10-23/`;
the original October 2 paper remains in `paper/original-2026-10-02/`.

## Repository guide

- [`paper/`](paper/README.md): 12-page English paper, revised October 26, 2026, standalone LaTeX, and build instructions
- [`Erdos143/`](Erdos143/): 61 Lean modules, including two analytic proofs and the real-domain conclusion
- [`Erdos143.lean`](Erdos143.lean): umbrella import for the complete formalization
- [`docs/`](docs/README.md): proof roadmap and paper-to-code correspondence
- [`scripts/`](scripts/): bootstrap, verification, integrity and axiom checks, paper typesetting
- [`verification/`](verification/README.md): two original local verification records, source hashes, and frozen archive
- [`CITATION.cff`](CITATION.cff): author, title, date, and repository citation metadata

The repository is focused on this proof. Exploratory alternatives and later
probabilistic extensions are not prerequisites and are not included.

## Authorship, assistance, and reuse

The paper is attributed to **Mattia Apicella**. AI assistance was used in
mathematical exploration, formalization, and exposition. The checked Lean
statements and recorded evidence, rather than an AI assessment, support the
formal-verification claims. Human mathematical review remains important.

Please cite the title and author in [CITATION.cff](CITATION.cff), together with
the exact commit you used. The preprint is deposited at
https://doi.org/10.5281/zenodo.23676536; the DOI for all versions is
https://doi.org/10.5281/zenodo.23671024. No open-source license has been selected for this repository;
contact the author about reuse. Lean and mathlib retain their own licenses.
