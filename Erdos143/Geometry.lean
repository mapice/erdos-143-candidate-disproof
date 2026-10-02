import Erdos143.Definitions

noncomputable section
open scoped BigOperators ENNReal

namespace Erdos143

lemma original_mono {A B : Set ℚ} (hB : Original B) (hAB : A ⊆ B) : Original A := by
  intro a ha b hb hab k hk
  exact hB a (hAB ha) b (hAB hb) hab k hk

lemma original_empty : Original ∅ := by
  intro a ha
  simp at ha

lemma original_union {A B : Set ℚ} (hA : Original A) (hB : Original B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, ∀ k : ℕ, 1 ≤ k → 1 ≤ |(k : ℚ) * a - b|)
    (hBA : ∀ b ∈ B, ∀ a ∈ A, ∀ k : ℕ, 1 ≤ k → 1 ≤ |(k : ℚ) * b - a|) :
    Original (A ∪ B) := by
  intro a ha b hb hab k hk
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact hA a ha b hb hab k hk
  · exact hAB a ha b hb k hk
  · exact hBA a ha b hb k hk
  · exact hB a ha b hb hab k hk

lemma new_source_separated {a b : ℚ} (hb : 0 ≤ b) (hab : a + 1 < b)
    {k : ℕ} (hk : 1 ≤ k) : 1 < |(k : ℚ) * b - a| := by
  have hkq : (1 : ℚ) ≤ k := by exact_mod_cast hk
  have hmul : b ≤ (k : ℚ) * b := by nlinarith
  have hpos : 0 < (k : ℚ) * b - a := by linarith
  rw [abs_of_pos hpos]
  linarith

/-- The fixed-denominator gap used for all multipliers simultaneously. -/
lemma rational_grid_gap {B : ℕ} (hB : 0 < B) {z : ℤ}
    (hz : (1 : ℚ) < (z : ℚ) / B) : 1 + 1 / (B : ℚ) ≤ (z : ℚ) / B := by
  have hBq : (0 : ℚ) < B := by exact_mod_cast hB
  have hlt : (B : ℚ) < z := by simpa using (lt_div_iff₀ hBq).mp hz
  have hzint : (B : ℤ) + 1 ≤ z := by
    have : (B : ℤ) < z := by exact_mod_cast hlt
    omega
  have hzq : (B : ℚ) + 1 ≤ z := by exact_mod_cast hzint
  apply (le_div_iff₀ hBq).2
  calc
    (1 + 1 / (B : ℚ)) * B = B + 1 := by field_simp
    _ ≤ z := hzq

/-- Moving a free lattice point a small positive distance preserves its old-source gap. -/
lemma right_perturbation_safe {B : ℕ} (hB : 0 < B) {z : ℤ} {η : ℚ}
    (hfree : ¬ ((-1 : ℚ) < (z : ℚ) / B ∧ (z : ℚ) / B ≤ 1))
    (hη : 0 < η) (hηB : η < 1 / (B : ℚ)) :
    1 < |(z : ℚ) / B - η| := by
  by_cases hlo : (z : ℚ) / B ≤ -1
  · have hneg : (z : ℚ) / B - η < 0 := by linarith
    rw [abs_of_neg hneg]
    linarith
  · have hhi : (1 : ℚ) < (z : ℚ) / B := by
      by_contra! h
      exact hfree ⟨lt_of_not_ge hlo, h⟩
    have hgap := rational_grid_gap hB hhi
    have hpos : 0 < (z : ℚ) / B - η := by linarith
    rw [abs_of_pos hpos]
    linarith

/-- Separation inside a scaled primitive block, including both pair orders. -/
lemma scaled_primitive_original {P : Set ℕ} (hP : Primitive P) {c : ℚ}
    (hc : 1 ≤ c) : Original ((fun n : ℕ => c * n) '' P) := by
  intro a ha b hb hab k hk
  rcases ha with ⟨m, hm, rfl⟩
  rcases hb with ⟨n, hn, rfl⟩
  have hmn : m ≠ n := by rintro rfl; exact hab rfl
  have hdiff : (k : ℤ) * m - n ≠ 0 := by
    intro hzero
    have heq : n = m * k := by
      have heq' : (k : ℤ) * m = n := by omega
      exact_mod_cast (heq'.symm.trans (mul_comm _ _))
    have hdvd : m ∣ n := ⟨k, heq⟩
    exact hmn (hP m hm n hn hdvd)
  have habs : (1 : ℚ) ≤ |(k : ℚ) * m - n| := by
    have hi : (1 : ℤ) ≤ |(k : ℤ) * m - n| := by
      have : 0 < |(k : ℤ) * m - n| := abs_pos.mpr hdiff
      omega
    exact_mod_cast hi
  have hc0 : 0 ≤ c := by linarith
  calc
    1 ≤ c * |(k : ℚ) * m - n| := by nlinarith
    _ = |c * ((k : ℚ) * m - n)| := by rw [abs_mul, abs_of_nonneg hc0]
    _ = |(k : ℚ) * (c * m) - c * n| := by congr 1; ring

/-- The lattice-gap argument applied to a rational source in any (not necessarily reduced)
representation. Its statement quantifies over all integer multipliers. -/
lemma old_source_perturbation_safe {A : ℤ} {B : ℕ} (hB : 0 < B) {m : ℤ} {η : ℚ}
    (hfree : ∀ k : ℤ, ¬ ((-1 : ℚ) < k * ((A : ℚ) / B) - m ∧
      k * ((A : ℚ) / B) - m ≤ 1))
    (hη : 0 < η) (hηB : η < 1 / (B : ℚ)) :
    ∀ k : ℤ, 1 < |k * ((A : ℚ) / B) - ((m : ℚ) + η)| := by
  intro k
  have hid : (((k * A - m * B : ℤ) : ℚ) / B) = k * ((A : ℚ) / B) - m := by
    push_cast
    field_simp
  have hfree' : ¬ ((-1 : ℚ) < ((k * A - m * B : ℤ) : ℚ) / B ∧
      ((k * A - m * B : ℤ) : ℚ) / B ≤ 1) := by rw [hid]; exact hfree k
  have h := right_perturbation_safe hB hfree' hη hηB
  rw [hid] at h
  convert h using 2
  ring

/-- The discrete numerator in the private-prime argument is nonzero for every integer k. -/
lemma private_prime_numerator_ne_zero {H t q n : ℕ} (hH : H.Prime)
    (ht : ¬ H ∣ t) (hq : ¬ H ∣ q) (hn : ¬ H ∣ n) (k : ℤ) :
    k * H - (t : ℤ) * q * n ≠ 0 := by
  intro hz
  have hdZ : (H : ℤ) ∣ (t : ℤ) * q * n := ⟨k, by nlinarith⟩
  have hdN : H ∣ t * q * n := by exact_mod_cast hdZ
  exact (hH.not_dvd_mul (hH.not_dvd_mul ht hq) hn) hdN

/-- The exact private-grid spacing bound, with no assumption that a rational presentation
is reduced and no upper bound on the integer multiplier. -/
lemma private_grid_separated {H t q n D : ℕ} {a : ℚ} (hH : H.Prime)
    (ht : ¬ H ∣ t) (hq : ¬ H ∣ q) (hn : ¬ H ∣ n)
    (hspacing : 4 < a / H)
    (hrelation : (D : ℚ) * H = a * t * q) (k : ℤ) :
    4 < |(k : ℚ) * a - (D : ℚ) * n| := by
  have hHq : (H : ℚ) ≠ 0 := by exact_mod_cast hH.ne_zero
  have hid : (k : ℚ) * a - (D : ℚ) * n =
      (a / H) * ((k * H - (t : ℤ) * q * n : ℤ) : ℚ) := by
    push_cast
    field_simp
    nlinarith [hrelation]
  have hz := private_prime_numerator_ne_zero hH ht hq hn k
  have hi : (1 : ℤ) ≤ |k * H - (t : ℤ) * q * n| := by
    have := abs_pos.mpr hz
    omega
  have hiq : (1 : ℚ) ≤ |((k * H - (t : ℤ) * q * n : ℤ) : ℚ)| := by
    exact_mod_cast hi
  have haspace : 0 ≤ a / H := by linarith
  rw [hid, abs_mul, abs_of_nonneg haspace]
  nlinarith

/-- The natural-number formulation has exactly the same positive-integer quantifiers. -/
lemma original_iff_integer_multipliers (A : Set ℚ) :
    Original A ↔ ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      ∀ k : ℤ, 1 ≤ k → 1 ≤ |(k : ℚ) * a - b| := by
  constructor
  · intro h a ha b hb hab k hk
    have hk0 : 0 ≤ k := by omega
    have hcast : ((k.toNat : ℕ) : ℚ) = (k : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg hk0
    have hkn : 1 ≤ k.toNat := by omega
    simpa [hcast] using h a ha b hb hab k.toNat hkn
  · intro h a ha b hb hab k hk
    have hkZ : (1 : ℤ) ≤ k := by exact_mod_cast hk
    simpa using h a ha b hb hab (k : ℤ) hkZ

/-- The rational inequalities are exactly the corresponding inequalities in the reals. -/
lemma original_iff_real_inequalities (A : Set ℚ) :
    Original A ↔ ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      ∀ k : ℕ, 1 ≤ k → (1 : ℝ) ≤ |(k : ℝ) * (a : ℝ) - (b : ℝ)| := by
  constructor
  · intro h a ha b hb hab k hk
    exact_mod_cast h a ha b hb hab k hk
  · intro h a ha b hb hab k hk
    exact_mod_cast h a ha b hb hab k hk

end Erdos143
