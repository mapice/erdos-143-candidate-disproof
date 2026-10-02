import Erdos143.Definitions
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Set

namespace Erdos143

lemma weight_integrand_factorization {n : ℝ} (hn : 1 < n) (t : ℝ) :
    n ^ (-(1 + t)) = n⁻¹ * Real.exp ((-Real.log n) * t) := by
  have hn0 : 0 < n := by linarith
  rw [Real.rpow_def_of_pos hn0]
  calc
    Real.exp (Real.log n * -(1 + t)) = Real.exp (-Real.log n + (-Real.log n) * t) := by
      congr 1
      ring
    _ = Real.exp (-Real.log n) * Real.exp ((-Real.log n) * t) := Real.exp_add _ _
    _ = n⁻¹ * Real.exp ((-Real.log n) * t) := by rw [Real.exp_neg, Real.exp_log hn0]

/-- The elementary integral identity behind the nonnegative interchange in §3.1. -/
lemma real_weight_integral {n : ℝ} (hn : 1 < n) :
    (∫ t : ℝ in Ioi 0, n ^ (-(1 + t))) = 1 / (n * Real.log n) := by
  have hlog : 0 < Real.log n := Real.log_pos hn
  simp_rw [weight_integrand_factorization hn]
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -Real.log n < 0) 0]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div, mul_inv_rev]
  ring

lemma weight_integrand_integrable {n : ℝ} (hn : 1 < n) :
    IntegrableOn (fun t : ℝ => n ^ (-(1 + t))) (Ioi 0) := by
  simp_rw [weight_integrand_factorization hn]
  exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos (Real.log_pos hn)) 0).const_mul _

end Erdos143
