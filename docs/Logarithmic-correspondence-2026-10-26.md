# The logarithmic analytic proof

The October 26 revision supplies a second formal proof of the periodic
primitive-selection lemma used in the construction. The original 55 modules
remain unchanged. The six additional modules use the same generating series,
weights, residue classes and final `PeriodicPrimitiveSelection` definition.
Lean remains pinned to 4.24.0 and mathlib to
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.

## The closed statement

`Erdos143.Logarithmic.periodicPrimitiveSelection_logarithmic_proved` has type
`Erdos143.PeriodicPrimitiveSelection`, with no analytic or construction
hypotheses. The `Estimate` class in intermediate lemmas is a proof interface:
the closing theorem constructs its instance from `remainderBound_proved`.
It is not an added axiom or an unproved condition on the conclusion.

This second theorem proves the analytic selection input. The original closed
existence theorems and their construction remain available with their original
proofs. The main mathematical statement and all constants are unchanged.

## Equation-to-code correspondence

| Paper, Section 3 | Formal declaration |
| --- | --- |
| Generating Euler product in Re(s)>1 | `generatingValue_eq_exp_log` |
| Real logarithm of the generating norm | `generatingValue_logarithmic_identity` |
| Cancellation of the linear Taylor term | `hasSum_logarithmicEulerFactorRemainder` |
| The iterated double series for R | `logarithmicEulerRemainder_eq_tsum_tsum` |
| Joint absolute convergence and uniform sum of norms ≤1−u | `logarithmicEulerDoubleSeries_abs_summable_and_tsum_le` |
| The uniform bound ‖R‖≤1−u for actual character factors | `Logarithmic.remainderBound_proved` |
| Nonprincipal generating bound | `Logarithmic.Bounds.nonprincipal_generatingValue_bounded` |
| Principal lower bound, including factor 1/2 and u≥1/2 | `Logarithmic.Bounds.principal_generating_local_lower` |
| Integrability of G−1 and the weighted series identity | `Logarithmic.generatingValue_sub_one_integrable`, `Logarithmic.integratedGeneratingValue_eq_weighted_series` |
| Vanishing normalized nonprincipal contribution | `Logarithmic.nonprincipal_normalized_integral_tendsto_zero` |
| Principal lower limit κ/4 | `Logarithmic.principal_abel_lower_bound` |
| Coprime residues | `Logarithmic.coprime_progression_abel_lower_bound` |
| All residues, including modulus 1 | `Logarithmic.all_residues_abel_lower_bound` |
| Finite primitive extraction with weight >1/6 | `Logarithmic.periodicPrimitiveSelection_logarithmic_proved` |

All names in the table are in namespace `Erdos143`. The Taylor index `n`
represents degree `n+2`, so the formal double series starts exactly at j=2.
The local complex logarithms occur only in individual Euler factors of norm
less than one. No choice of a complex logarithm of the global L-function,
or nonvanishing at s=1, is used.

The unrestricted generating bound is proved on `0<t≤ε₀` for some fixed
`ε₀∈(0,1]`. The article now states this same local interval; continuity handles
the compact interval between it and the exponentially decreasing tail.
The standard summability of `1/(n log² n)`, used for the logarithmic shift,
is established in Lean through a Mellin moment integral rather than the
integral-test sentence used in the article. Both prove the same input.

## Verification

The project contains 61 modules and 319 proved declarations. Run

```sh
bash scripts/verify.sh
bash scripts/verify-manuscript.sh
bash scripts/verify-logarithmic.sh
```

The last command checks the closed selection theorem and traverses its
project dependencies. It requires the new logarithmic identity and uniform
remainder theorem, and rejects a list of the original Euler comparisons and
the original closed selection theorem. Importing a module that also contains
the earlier proof does not imply that the new proof depends on those terms.

The axiom audits permit only `propext`, `Classical.choice` and `Quot.sound`.
These are local kernel checks of the stated formal results, not an independent
human review, a literature-priority assessment or journal acceptance.

The October 2 and October 23 records remain historical evidence for their
original sources. The new record is under `verification/2026-10-26/`.
The old proof manifest is preserved there as `baseline-proof-SHA256SUMS`;
the root `verification/proof-SHA256SUMS` identifies the current proof inputs.
