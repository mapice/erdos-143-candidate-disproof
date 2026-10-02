# Reading the proof

Start with the [paper](../paper/erdos143-candidate.pdf), then inspect the
[explicit real-domain theorem](../Erdos143/RealConclusion.lean).

- [Abel-average primitive selection](Abel-periodic-proof.md) explains the
  analytic input, including the uniform character bounds and finite extraction
- [Construction correspondence](Construction-correspondence.md) explains the
  private primes, closed filters, product grid, finite extensions, and union

These two notes originated during development. References to the “original
candidate” or “manuscript's stronger” intermediate statements refer to earlier
drafts. The paper included in this repository has been updated to the proved
Abel-average route, closed root filter, finite reciprocal-prime budget, product
reset grid, and non-strict round gain. No earlier draft is needed.

## Entry points in the Lean sources

| Part | Source |
| --- | --- |
| Definitions and exact rational conclusions | [Definitions.lean](../Erdos143/Definitions.lean) |
| Periodic primitive-selection theorem | [PeriodicSelection.lean](../Erdos143/PeriodicSelection.lean) |
| Valid finite construction states | [ConstructionState.lean](../Erdos143/ConstructionState.lean) |
| Simultaneous block invariants | [BlockExtension.lean](../Erdos143/BlockExtension.lean) |
| Existence of an insertion | [InsertionExistence.lean](../Erdos143/InsertionExistence.lean) |
| Existence of a complete round | [RoundExtension.lean](../Erdos143/RoundExtension.lean) |
| Recursion, nested union, and infinite mass | [Main.lean](../Erdos143/Main.lean) |
| Rational-to-real transfer and nonsummability | [RealConclusion.lean](../Erdos143/RealConclusion.lean) |

The paper's “Verification scope and reproducibility” subsection provides a
more detailed declaration mapping. For exact environmental assumptions and
local evidence, see [verification](../verification/README.md).
