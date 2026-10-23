import Erdos143.RealConclusion

/-!
Additional statement checks for the October 23 manuscript.
These examples expose the exact strong statement and the common recursive
witness. They add no assumption and do not change the frozen proof sources.
Run from the project root:
  lake env lean -DwarningAsError=true submission/blms-2026-10-23/ManuscriptAudit.lean
-/

open scoped ENNReal

example : ∃ A : Set ℚ, A.Countable ∧ (∀ a ∈ A, (2 : ℚ) ≤ a) ∧
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ k : ℕ, 1 ≤ k → 1 ≤ |(k : ℚ) * a - b|) ∧
    (∑' a : A, ENNReal.ofReal (1 / ((a.val : ℝ) * Real.log a.val))) = ⊤ ∧
    (∀ x : ℚ, (A ∩ Set.Iic x).Finite) ∧
    (∀ a ∈ A, ∃ m : ℕ, 2 ≤ m ∧ 0 < a - m ∧
      a - m ≤ 1 / (2 * (m : ℚ) ^ 12)) :=
  Erdos143.strongConclusion_proved

example : Monotone Erdos143.pointSequence :=
  Erdos143.pointSequence_monotone

example (R : ℕ) :
    (R : ℝ≥0∞) / 576 ≤ (Erdos143.stateSequence R).val.mass :=
  Erdos143.stateSequence_mass_lower R

example : Erdos143.Original Erdos143.constructedSet :=
  Erdos143.constructedSet_original

example : Erdos143.totalWeight Erdos143.constructedSet = ⊤ :=
  Erdos143.constructedSet_weight_diverges

example : Erdos143.LocallyFiniteAbove Erdos143.constructedSet :=
  Erdos143.original_locallyFiniteAbove Erdos143.constructedSet_original
    Erdos143.constructedSet_lower

example : ∀ a ∈ Erdos143.constructedSet,
    Erdos143.TinyPositiveDisplacement a :=
  Erdos143.constructedSet_tiny

example : ∃ A : Set ℝ, A.Countable ∧ A ⊆ Set.Ici 2 ∧
    (∀ a ∈ A, ∃ q : ℚ, a = (q : ℝ)) ∧
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ k : ℕ, 1 ≤ k →
      1 ≤ |(k : ℝ) * a - b|) ∧
    (∑' a : A, ENNReal.ofReal (1 / (a.val * Real.log a.val))) = ⊤ ∧
    ¬ Summable (fun a : A => 1 / (a.val * Real.log a.val)) :=
  Erdos143.realConclusion_proved

#print axioms Erdos143.mainConclusion_proved
#print axioms Erdos143.strongConclusion_proved
#print axioms Erdos143.realConclusion_proved


/-- A single witness supplies every manuscript conclusion, including infinitude
and the very same finite prefixes with their weight bound. This is a corollary
of the frozen proof, not an extra assumption supplied to it. -/
theorem Erdos143.manuscript_full_statement :
    ∃ A : Set ℚ, ∃ F : ℕ → Finset ℚ,
      A.Countable ∧ A.Infinite ∧ (∀ a ∈ A, (2 : ℚ) ≤ a) ∧
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ k : ℕ, 1 ≤ k →
        1 ≤ |(k : ℚ) * a - b|) ∧
      (∑' a : A, ENNReal.ofReal (1 / ((a.val : ℝ) * Real.log a.val))) = ⊤ ∧
      (∀ x : ℚ, (A ∩ Set.Iic x).Finite) ∧
      (∀ a ∈ A, ∃ m : ℕ, 2 ≤ m ∧ 0 < a - m ∧
        a - m ≤ 1 / (2 * (m : ℚ) ^ 12)) ∧
      Monotone (fun R => (F R : Set ℚ)) ∧
      (∀ R, ∀ a ∈ F R, ∀ b ∈ F R, a ≠ b → ∀ k : ℕ, 1 ≤ k →
        1 ≤ |(k : ℚ) * a - b|) ∧
      (∀ R : ℕ, (R : ℝ≥0∞) / 576 ≤
        ∑ a ∈ F R, ENNReal.ofReal (1 / ((a : ℝ) * Real.log a))) ∧
      A = ⋃ R, (F R : Set ℚ) := by
  classical
  have hinfinite : Erdos143.constructedSet.Infinite := by
    intro hfinite
    have hfiniteweight : Erdos143.totalWeight Erdos143.constructedSet ≠ ⊤ := by
      rw [← hfinite.coe_toFinset, Erdos143.totalWeight_finset]
      exact ENNReal.sum_ne_top.mpr (fun a _ => ENNReal.ofReal_ne_top)
    exact hfiniteweight Erdos143.constructedSet_weight_diverges
  refine ⟨Erdos143.constructedSet, fun R => (Erdos143.stateSequence R).val.points,
    Erdos143.rational_set_countable _, hinfinite, Erdos143.constructedSet_lower,
    Erdos143.constructedSet_original, Erdos143.constructedSet_weight_diverges,
    Erdos143.original_locallyFiniteAbove Erdos143.constructedSet_original
      Erdos143.constructedSet_lower,
    Erdos143.constructedSet_tiny, Erdos143.pointSequence_monotone, ?_, ?_, rfl⟩
  · intro R
    exact (Erdos143.stateSequence R).property.original
  · intro R
    exact Erdos143.stateSequence_mass_lower R

#print axioms Erdos143.manuscript_full_statement
