import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Data.Rat.Encodable
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact statements for the candidate for Erdős problem 143

This file defines the requested conclusion; it does not assert or prove it.
The weight is summed in `ENNReal`, so a divergent nonnegative series is
represented by `⊤`, rather than by Lean's default value for a divergent real tsum.
-/

noncomputable section
open scoped BigOperators ENNReal

namespace Erdos143

/-- The quantifiers are over ordered distinct pairs and every positive integer. -/
def Original (A : Set ℚ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ k : ℕ, 1 ≤ k → 1 ≤ |(k : ℚ) * a - b|

/-- The nonnegative version of the logarithmic weight. -/
def weight (a : ℚ) : ℝ≥0∞ := ENNReal.ofReal (1 / ((a : ℝ) * Real.log a))

def totalWeight (A : Set ℚ) : ℝ≥0∞ := ∑' a : A, weight a

/-- A primitive set of natural numbers, with the lower bound recorded separately. -/
def Primitive (P : Set ℕ) : Prop :=
  ∀ m ∈ P, ∀ n ∈ P, m ∣ n → m = n

/-- Every bounded initial interval contains only finitely many points. -/
def LocallyFiniteAbove (A : Set ℚ) : Prop :=
  ∀ x : ℚ, (A ∩ Set.Iic x).Finite

/-- The additional small positive displacement in the candidate. -/
def TinyPositiveDisplacement (a : ℚ) : Prop :=
  ∃ m : ℕ, 2 ≤ m ∧ 0 < a - m ∧ a - m ≤ 1 / (2 * (m : ℚ) ^ 12)

/-- The exact main existence claim. No proof is supplied by this definition. -/
def MainConclusion : Prop :=
  ∃ A : Set ℚ, A.Countable ∧ (∀ a ∈ A, (2 : ℚ) ≤ a) ∧
    Original A ∧ totalWeight A = ⊤

/-- The stronger existence claim made by the manuscript. -/
def StrongConclusion : Prop :=
  ∃ A : Set ℚ, A.Countable ∧ (∀ a ∈ A, (2 : ℚ) ≤ a) ∧
    Original A ∧ totalWeight A = ⊤ ∧ LocallyFiniteAbove A ∧
    ∀ a ∈ A, TinyPositiveDisplacement a

/-- Free lattice labels; the half-open interval is deliberately asymmetric. -/
def RightFree (F : Set ℚ) (D : ℕ) (n : ℕ) : Prop :=
  ∀ a ∈ F, ∀ k : ℤ, ¬ ((-1 : ℚ) < k * a - D * n ∧ k * a - D * n ≤ 1)

/-- The analytic finite-selection interface, proved by `periodicPrimitiveSelection_proved`. -/
def PeriodicPrimitiveSelection : Prop :=
  ∀ (L : ℕ) (_ : 0 < L) (S : Finset (Fin L)),
    (2 / 3 : ℚ) < (S.card : ℚ) / L →
    ∀ N : ℕ, 2 ≤ N → ∃ P : Finset ℕ,
      (∀ n ∈ P, N ≤ n ∧ (⟨n % L, Nat.mod_lt _ ‹0 < L›⟩ : Fin L) ∈ S) ∧
      Primitive (P : Set ℕ) ∧
      (1 / 6 : ℝ≥0∞) < ∑ n ∈ P, weight n

end Erdos143
