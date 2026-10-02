import Erdos143.Main

noncomputable section
open scoped ENNReal
namespace Erdos143

/-- The actual subset of the reals is the injective image of the rational construction. -/
def constructedRealSet : Set ℝ := (fun q : ℚ => (q : ℝ)) '' constructedSet

def constructedRealEquiv : constructedSet ≃ constructedRealSet :=
  Equiv.ofBijective (fun a => ⟨(a.val : ℝ), ⟨a.val, a.property, rfl⟩⟩)
    ⟨by
      intro a b hab
      apply Subtype.ext
      exact Rat.cast_injective (congrArg Subtype.val hab),
    by
      intro a
      obtain ⟨q, hq, heq⟩ := a.property
      exact ⟨⟨q, hq⟩, Subtype.ext heq⟩⟩

lemma constructedRealSet_lower : ∀ a ∈ constructedRealSet, (2 : ℝ) ≤ a := by
  intro a ha
  obtain ⟨q, hq, rfl⟩ := ha
  change (2 : ℝ) ≤ (q : ℝ)
  exact_mod_cast constructedSet_lower q hq

lemma constructedRealSet_separated :
    ∀ a ∈ constructedRealSet, ∀ b ∈ constructedRealSet, a ≠ b →
      ∀ k : ℕ, 1 ≤ k → (1 : ℝ) ≤ |(k : ℝ) * a - b| := by
  intro a ha b hb hab k hk
  obtain ⟨q, hq, rfl⟩ := ha
  obtain ⟨r, hr, rfl⟩ := hb
  have hqr : q ≠ r := fun h => hab (congrArg (fun x : ℚ => (x : ℝ)) h)
  exact (original_iff_real_inequalities constructedSet).mp constructedSet_original q hq r hr hqr k hk

lemma constructedRealSet_weight_diverges :
    (∑' a : constructedRealSet, ENNReal.ofReal (1 / (a.val * Real.log a.val))) = ⊤ := by
  rw [← constructedRealEquiv.tsum_eq (fun a : constructedRealSet =>
    ENNReal.ofReal (1 / (a.val * Real.log a.val)))]
  exact constructedSet_weight_diverges

lemma constructedRealSet_not_summable :
    ¬ Summable (fun a : constructedRealSet => 1 / (a.val * Real.log a.val)) := by
  intro hs
  have hn (a : constructedRealSet) : 0 ≤ 1 / (a.val * Real.log a.val) := by
    have ha := constructedRealSet_lower a a.property
    have hlog : 0 < Real.log a.val := Real.log_pos (by linarith)
    positivity
  have h := ENNReal.ofReal_tsum_of_nonneg hn hs
  rw [constructedRealSet_weight_diverges] at h
  exact ENNReal.ofReal_ne_top h

/-- A completely explicit real-domain formulation, including rationality, countability,
all ordered positive-integer multiplier inequalities, and divergence of the nonnegative sum. -/
theorem realConclusion_proved :
    ∃ A : Set ℝ, A.Countable ∧ A ⊆ Set.Ici 2 ∧
      (∀ a ∈ A, ∃ q : ℚ, a = (q : ℝ)) ∧
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ k : ℕ, 1 ≤ k → 1 ≤ |(k : ℝ) * a - b|) ∧
      (∑' a : A, ENNReal.ofReal (1 / (a.val * Real.log a.val))) = ⊤ ∧
      ¬ Summable (fun a : A => 1 / (a.val * Real.log a.val)) := by
  refine ⟨constructedRealSet, (rational_set_countable constructedSet).image _,
    constructedRealSet_lower, ?_, constructedRealSet_separated,
    constructedRealSet_weight_diverges, constructedRealSet_not_summable⟩
  intro a ha
  obtain ⟨q, _, rfl⟩ := ha
  exact ⟨q, rfl⟩

end Erdos143
