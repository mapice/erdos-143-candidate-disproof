import Erdos143.Weight
import Erdos143.NestedUnion

noncomputable section
open scoped ENNReal BigOperators

namespace Erdos143

/-- The finite primitive-selection weight, once supplied, yields the exact claimed block gain.
Primitivity is irrelevant to this weight calculation and is handled separately by geometry. -/
lemma block_weight_lower_bound (P : Finset ℕ) {c : ℚ} {D : ℕ}
    (hc : 1 < c) (hc2 : c < 2) (hD : 1 ≤ D) (hn : ∀ n ∈ P, 2 * D ≤ n)
    (hweight : (1 / 6 : ℝ≥0∞) < ∑ n ∈ P, weight n) :
    (1 : ℝ≥0∞) / (24 * D) <
      totalWeight ((P.image (fun n : ℕ => c * D * n) : Finset ℚ) : Set ℚ) := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast (by omega : 0 < D)
  have hcq : (0 : ℚ) < c := by linarith
  have hcD : c * (D : ℚ) ≠ 0 := ne_of_gt (mul_pos hcq hDq)
  have hinj : Function.Injective (fun n : ℕ => c * D * n) := by
    intro n m hnm
    exact_mod_cast (mul_left_cancel₀ hcD hnm)
  have himage : totalWeight ((P.image (fun n : ℕ => c * D * n) : Finset ℚ) : Set ℚ) =
      ∑ n ∈ P, weight (c * D * n) := by
    rw [totalWeight_finset, Finset.sum_image]
    intro a ha b hb hab
    exact hinj hab
  have hsum : (∑ n ∈ P, weight n) / (4 * (D : ℝ≥0∞)) ≤
      ∑ n ∈ P, weight (c * D * n) := by
    calc
      _ = ∑ n ∈ P, weight n / (4 * (D : ℝ≥0∞)) := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
      _ ≤ _ := Finset.sum_le_sum (fun n hnp => scaled_weight_lower_bound hc hc2 hD (hn n hnp))
  have hD0 : (4 * (D : ℝ≥0∞)) ≠ 0 := by
    have hd : D ≠ 0 := by omega
    simp [hd]
  have hDt : (4 * (D : ℝ≥0∞)) ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) (by simp)
  rw [himage]
  calc
    (1 : ℝ≥0∞) / (24 * D) = (1 / 6) / (4 * (D : ℝ≥0∞)) := by
      rw [show (24 : ℝ≥0∞) * D = 6 * (4 * D) by ring]
      simp only [div_eq_mul_inv, one_mul]
      exact ENNReal.mul_inv (a := 6) (b := 4 * D) (Or.inl (by norm_num)) (Or.inl (by norm_num))
    _ < (∑ n ∈ P, weight n) / (4 * (D : ℝ≥0∞)) :=
      ENNReal.div_lt_div_right hD0 hDt hweight
    _ ≤ _ := hsum

end Erdos143
