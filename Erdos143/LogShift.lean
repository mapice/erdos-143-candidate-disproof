import Erdos143.LogWeights
import Erdos143.MomentIntegrability

noncomputable section
open scoped ArithmeticFunction.Omega

namespace Erdos143

def momentWeight (n : ℕ) : ℝ := 1 / ((n : ℝ) * (Real.log n) ^ 2)
@[simp] lemma momentWeight_zero : momentWeight 0 = 0 := by simp [momentWeight]
@[simp] lemma momentWeight_one : momentWeight 1 = 0 := by simp [momentWeight]

lemma momentWeight_nonneg (n : ℕ) : 0 ≤ momentWeight n := by unfold momentWeight; positivity

lemma momentWeight_summable : Summable momentWeight := by
  apply (summable_nat_add_iff 2).mp
  simpa only [momentWeight, Nat.cast_add, Nat.cast_ofNat] using log_squared_weight_summable

/-- The elementary logarithmic-shift loss, with both its sign and its summable bound. -/
lemma log_shift_difference {x y : ℝ} (hx : 1 < x) (hy : 0 ≤ y) :
    0 ≤ 1 / (x * Real.log x) - 1 / (x * (Real.log x + y)) ∧
    1 / (x * Real.log x) - 1 / (x * (Real.log x + y)) ≤ y / (x * (Real.log x) ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  have hly : 0 < Real.log x + y := by linarith
  constructor
  · apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  · have hid : 1 / (x * Real.log x) - 1 / (x * (Real.log x + y)) =
        y / (x * Real.log x * (Real.log x + y)) := by field_simp; ring
    rw [hid]
    apply div_le_div_of_nonneg_left hy (by positivity)
    nlinarith [mul_nonneg (mul_nonneg hx0.le hl.le) hy]

lemma natWeight_mul_formula {g m : ℕ} (hg : 1 ≤ g) (hm : 2 ≤ m) :
    natWeight (g * m) = (g : ℝ)⁻¹ * (1 / ((m : ℝ) * (Real.log m + Real.log g))) := by
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  unfold natWeight
  rw [Nat.cast_mul, Real.log_mul hg0 hm0]
  simp only [one_div, mul_inv_rev]
  ring

lemma realAbelTerm_mul_lower_of_two_le {g m : ℕ} (hg : 1 ≤ g) (hm : 2 ≤ m)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (u ^ Ω g / (g : ℝ)) * realAbelTerm u m - (Real.log g / (g : ℝ)) * momentWeight m ≤
      realAbelTerm u (g * m) := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hmR : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hlg : 0 ≤ Real.log (g : ℝ) := Real.log_nonneg (by exact_mod_cast hg)
  have hA0 : 0 ≤ u ^ Ω g := pow_nonneg hu0 _
  have hB0 : 0 ≤ u ^ Ω m := pow_nonneg hu0 _
  have hA1 : u ^ Ω g ≤ 1 := pow_le_one₀ hu0 hu1
  have hB1 : u ^ Ω m ≤ 1 := pow_le_one₀ hu0 hu1
  have hAB0 : 0 ≤ u ^ Ω g * u ^ Ω m := mul_nonneg hA0 hB0
  have hAB1 : u ^ Ω g * u ^ Ω m ≤ 1 := by nlinarith
  have hloss := (log_shift_difference hmR hlg).2
  have hloss0 : 0 ≤ Real.log g / ((m : ℝ) * (Real.log m) ^ 2) := by positivity
  have hcoeff := div_le_div_of_nonneg_right hAB1 hgR.le
  have hbound : (u ^ Ω g * u ^ Ω m / (g : ℝ)) *
      (natWeight m - 1 / ((m : ℝ) * (Real.log m + Real.log g))) ≤
      (Real.log g / (g : ℝ)) * momentWeight m := by
    calc
      _ ≤ (u ^ Ω g * u ^ Ω m / (g : ℝ)) *
          (Real.log g / ((m : ℝ) * (Real.log m) ^ 2)) :=
        mul_le_mul_of_nonneg_left hloss (div_nonneg hAB0 hgR.le)
      _ ≤ (1 / (g : ℝ)) * (Real.log g / ((m : ℝ) * (Real.log m) ^ 2)) :=
        mul_le_mul_of_nonneg_right hcoeff hloss0
      _ = _ := by unfold momentWeight; ring
  have hΩ := ArithmeticFunction.cardFactors_mul (by omega : g ≠ 0) (by omega : m ≠ 0)
  have hid : (u ^ Ω g / (g : ℝ)) * realAbelTerm u m - realAbelTerm u (g * m) =
      (u ^ Ω g * u ^ Ω m / (g : ℝ)) *
        (natWeight m - 1 / ((m : ℝ) * (Real.log m + Real.log g))) := by
    unfold realAbelTerm
    rw [hΩ, pow_add, natWeight_mul_formula hg hm]
    ring
  rw [← hid] at hbound
  linarith

lemma realAbelTerm_mul_lower {g m : ℕ} (hg : 1 ≤ g) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (u ^ Ω g / (g : ℝ)) * realAbelTerm u m - (Real.log g / (g : ℝ)) * momentWeight m ≤
      realAbelTerm u (g * m) := by
  by_cases hm : 2 ≤ m
  · exact realAbelTerm_mul_lower_of_two_le hg hm hu0 hu1
  · have hm' : m = 0 ∨ m = 1 := by omega
    rcases hm' with rfl | rfl
    · simp
    · simpa using realAbelTerm_nonneg hu0 g

end Erdos143
