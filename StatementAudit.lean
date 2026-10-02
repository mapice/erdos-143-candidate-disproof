import Erdos143.RealConclusion

open scoped ENNReal

example : ∃ A : Set ℚ, A.Countable ∧ (∀ a ∈ A, (2 : ℚ) ≤ a) ∧
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ k : ℕ, 1 ≤ k → 1 ≤ |(k : ℚ) * a - b|) ∧
    (∑' a : A, ENNReal.ofReal (1 / ((a.val : ℝ) * Real.log a.val))) = ⊤ :=
  Erdos143.mainConclusion_proved

example : ∃ A : Set ℝ, A.Countable ∧ A ⊆ Set.Ici 2 ∧
    (∀ a ∈ A, ∃ q : ℚ, a = (q : ℝ)) ∧
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ k : ℕ, 1 ≤ k → 1 ≤ |(k : ℝ) * a - b|) ∧
    (∑' a : A, ENNReal.ofReal (1 / (a.val * Real.log a.val))) = ⊤ ∧
    ¬ Summable (fun a : A => 1 / (a.val * Real.log a.val)) :=
  Erdos143.realConclusion_proved

#print axioms Erdos143.mainConclusion_proved
#print axioms Erdos143.strongConclusion_proved
#print axioms Erdos143.realConclusion_proved
