import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
These are checked applications of existing mathlib theorems. They are not a proof
of the bespoke weighted periodic-selection lemma.
-/

namespace Erdos143

/-- Nonvanishing on the real segment, including its endpoint at 1. -/
lemma nonprincipal_LFunction_nonzero_segment {L : ℕ} [NeZero L]
    (χ : DirichletCharacter ℂ L) (hχ : χ ≠ 1) {t : ℝ} (ht : 0 ≤ t) :
    χ.LFunction (1 + (t : ℂ)) ≠ 0 := by
  apply χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ)
  simpa using ht

/-- Continuation near the segment is available as an entire function for a nonprincipal character. -/
lemma nonprincipal_LFunction_continuous {L : ℕ} [NeZero L]
    (χ : DirichletCharacter ℂ L) (hχ : χ ≠ 1) : Continuous χ.LFunction :=
  (DirichletCharacter.differentiable_LFunction hχ).continuous

end Erdos143
