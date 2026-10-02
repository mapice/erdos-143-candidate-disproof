import Erdos143.Definitions

noncomputable section
open scoped BigOperators ENNReal

namespace Erdos143

/-- Every pair is captured by one prefix; the bound holds for every k, without a cutoff. -/
lemma original_iUnion_of_monotone {F : ℕ → Set ℚ} (hmono : Monotone F)
    (hF : ∀ i, Original (F i)) : Original (⋃ i, F i) := by
  intro a ha b hb hab k hk
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hb
  exact hF (max i j) a (hmono (le_max_left i j) hi)
    b (hmono (le_max_right i j) hj) hab k hk

/-- A rational set is countable without any extra enumeration hypothesis. -/
lemma rational_set_countable (A : Set ℚ) : A.Countable := Set.to_countable A

lemma lower_bound_iUnion {F : ℕ → Set ℚ} (hF : ∀ i, ∀ a ∈ F i, (2 : ℚ) ≤ a) :
    ∀ a ∈ ⋃ i, F i, (2 : ℚ) ≤ a := by
  intro a ha
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
  exact hF i a hi

lemma totalWeight_mono {A B : Set ℚ} (hAB : A ⊆ B) : totalWeight A ≤ totalWeight B := by
  let f : A → B := fun a => ⟨a.val, hAB a.property⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun x : B => x.val) h
  exact ENNReal.tsum_comp_le_tsum_of_injective hf (fun b : B => weight b)

/-- Arbitrarily large finite-prefix weights force the actual nonnegative series to diverge. -/
lemma totalWeight_iUnion_eq_top_of_unbounded {F : ℕ → Set ℚ}
    (hF : ∀ n : ℕ, ∃ i : ℕ, (n : ℝ≥0∞) < totalWeight (F i)) :
    totalWeight (⋃ i, F i) = ⊤ := by
  apply top_unique
  rw [← ENNReal.iSup_natCast]
  apply iSup_le
  intro n
  obtain ⟨i, hi⟩ := hF n
  exact hi.le.trans (totalWeight_mono (Set.subset_iUnion F i))

/-- The manuscript's precise round bound suffices; 576 is kept explicit. -/
lemma totalWeight_iUnion_eq_top_of_round_bound {F : ℕ → Set ℚ}
    (hF : ∀ R : ℕ, 1 ≤ R → (R : ℝ≥0∞) / 576 < totalWeight (F R)) :
    totalWeight (⋃ i, F i) = ⊤ := by
  apply totalWeight_iUnion_eq_top_of_unbounded
  intro n
  refine ⟨(n + 1) * 576, ?_⟩
  have hR : 1 ≤ (n + 1) * 576 := by omega
  have h := hF ((n + 1) * 576) hR
  have heq : (((n + 1) * 576 : ℕ) : ℝ≥0∞) / 576 = (n : ℝ≥0∞) + 1 := by
    push_cast
    exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
  rw [heq] at h
  exact (le_add_right le_rfl).trans_lt h

/-- For a finite prefix the subtype sum is exactly its usual finite sum. -/
lemma totalWeight_finset (F : Finset ℚ) : totalWeight (F : Set ℚ) = ∑ a ∈ F, weight a := by
  rw [totalWeight, tsum_fintype]
  exact Finset.sum_coe_sort F weight

end Erdos143
