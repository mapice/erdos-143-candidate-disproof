import Erdos143.MellinWeight
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

open MeasureTheory Set

namespace Erdos143

lemma real_log_moment_integral {n : ℝ} (hn : 1 < n) :
    (∫ t : ℝ in Ioi 0, t * n ^ (-(1 + t))) = 1 / (n * (Real.log n) ^ 2) := by
  have hlog := Real.log_pos hn
  have hgamma : Real.Gamma (2 : ℝ) = 1 := by
    simp
  have hI := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := Real.log n) (by norm_num) hlog
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, hgamma, mul_one] at hI
  have hfun : (fun t : ℝ => t * n ^ (-(1 + t))) =
      fun t : ℝ => n⁻¹ * (t * Real.exp (-(Real.log n * t))) := by
    funext t
    rw [weight_integrand_factorization hn]
    simp only [neg_mul]
    ring
  rw [hfun, integral_const_mul, hI]
  simp only [one_div, mul_inv_rev, inv_pow]
  ring

/-- A polynomial factor can be absorbed by halving an exponential decay rate. -/
lemma linear_exp_tail {c : ℝ} (hc : 0 < c) (t : ℝ) :
    t * Real.exp ((-c) * t) ≤ (2 / c) * Real.exp ((-(c / 2)) * t) := by
  have h : (c / 2) * t ≤ Real.exp ((c / 2) * t) := by
    linarith [Real.add_one_le_exp ((c / 2) * t)]
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos ((-c) * t)).le
  rw [← Real.exp_add] at hmul
  have he : (c / 2) * t + (-c) * t = (-(c / 2)) * t := by ring
  rw [he] at hmul
  calc
    t * Real.exp ((-c) * t) ≤ Real.exp ((-(c / 2)) * t) / (c / 2) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < c / 2)).2
      nlinarith [hmul]
    _ = _ := by field_simp

end Erdos143
