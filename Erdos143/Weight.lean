import Erdos143.Definitions

noncomputable section
open scoped ENNReal

namespace Erdos143

/-- The quantitative block estimate from §8, over the reals before taking nonnegative sums. -/
lemma scaled_real_weight_lower_bound {c D n : ℝ} (hc : 1 < c) (hc2 : c < 2)
    (hD : 1 ≤ D) (hn : 2 * D ≤ n) :
    (1 / (n * Real.log n)) / (4 * D) ≤ 1 / ((c * D * n) * Real.log (c * D * n)) := by
  have hD0 : 0 < D := by linarith
  have hn1 : 1 < n := by linarith
  have hn0 : 0 < n := by linarith
  have hc0 : 0 < c := by linarith
  have hcd1 : 1 ≤ c * D := by
    calc
      (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ c * D := mul_le_mul hc.le hD (by norm_num) hc0.le
  have hncn : n ≤ c * D * n := by
    simpa using mul_le_mul_of_nonneg_right hcd1 hn0.le
  have hcn : 1 < c * D * n := hn1.trans_le hncn
  have hcn0 : 0 < c * D * n := by positivity
  have hlogn : 0 < Real.log n := Real.log_pos hn1
  have hlogcn : 0 < Real.log (c * D * n) := Real.log_pos hcn
  have hcdn : c * D ≤ n := (mul_le_mul_of_nonneg_right hc2.le hD0.le).trans hn
  have hcnle : c * D * n ≤ n ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hcdn hn0.le]
  have hlog : Real.log (c * D * n) ≤ 2 * Real.log n := by
    have h := Real.log_le_log hcn0 hcnle
    rwa [Real.log_pow, Nat.cast_ofNat] at h
  have hscale : c * D * n ≤ 2 * D * n := by nlinarith
  have hprod := mul_le_mul hscale hlog hlogcn.le (by positivity : (0 : ℝ) ≤ 2 * D * n)
  have hden : (c * D * n) * Real.log (c * D * n) ≤ 4 * D * (n * Real.log n) := by
    nlinarith [hprod]
  calc
    (1 / (n * Real.log n)) / (4 * D) = 1 / (4 * D * (n * Real.log n)) := by
      rw [div_div]
      congr 1
      ring
    _ ≤ 1 / ((c * D * n) * Real.log (c * D * n)) :=
      one_div_le_one_div_of_le (by positivity) hden

/-- Positivity ensures that `ofReal` does not discard any term in the requested range. -/
lemma real_weight_pos {a : ℚ} (ha : (2 : ℚ) ≤ a) :
    0 < 1 / ((a : ℝ) * Real.log a) := by
  have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hlog : 0 < Real.log (a : ℝ) := Real.log_pos (by linarith)
  positivity

lemma weight_pos {a : ℚ} (ha : (2 : ℚ) ≤ a) : 0 < weight a := by
  exact ENNReal.ofReal_pos.mpr (real_weight_pos ha)

/-- Every individual term is finite; divergence cannot come from an infinite summand. -/
lemma weight_ne_top (a : ℚ) : weight a ≠ ⊤ := ENNReal.ofReal_ne_top

/-- A complete round contains enough blocks for the uniform gain. -/
lemma round_blocks_lower_bound {D : ℕ} (hD : 48 ≤ D) : (D : ℚ) / 24 ≤ ((D / 12 : ℕ) : ℚ) := by
  have hq : D < 12 * (D / 12 + 1) := Nat.lt_mul_div_succ D (by decide : 0 < 12)
  have hQ : 2 * (D / 12) * 12 ≥ D := by omega
  have hQrat : (2 : ℚ) * (D / 12 : ℕ) * 12 ≥ D := by exact_mod_cast hQ
  linarith

/-- The same block estimate for the actual extended-nonnegative weight used in the target. -/
lemma scaled_weight_lower_bound {c : ℚ} {D n : ℕ} (hc : 1 < c) (hc2 : c < 2)
    (hD : 1 ≤ D) (hn : 2 * D ≤ n) :
    weight n / (4 * (D : ℝ≥0∞)) ≤ weight (c * D * n) := by
  have hcR : (1 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hc2R : (c : ℝ) < 2 := by exact_mod_cast hc2
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hnR : (2 : ℝ) * D ≤ n := by exact_mod_cast hn
  have h := ENNReal.ofReal_le_ofReal (scaled_real_weight_lower_bound hcR hc2R hDR hnR)
  rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 4 * D)] at h
  simpa [weight, ENNReal.ofReal_mul, Nat.cast_nonneg] using h

end Erdos143
