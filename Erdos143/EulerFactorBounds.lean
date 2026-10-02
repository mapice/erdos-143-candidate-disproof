import Erdos143.Definitions
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
Elementary factor inequalities for an alternative Abel-average proof.
They do not assert the remaining infinite-product or periodic-selection result.
-/

namespace Erdos143

lemma rpow_one_add_le_linear {u x : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hx : 0 ≤ x) :
    (1 + x) ^ u ≤ 1 + u * x := by
  have h := Real.geom_mean_le_arith_mean2_weighted
    (w₁ := 1 - u) (w₂ := u) (p₁ := 1) (p₂ := 1 + x)
    (by linarith) hu0 (by norm_num) (by linarith) (by ring)
  simp only [Real.one_rpow, one_mul, mul_one] at h
  nlinarith

lemma rpow_one_sub_le_linear {u x : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hx : x < 1) :
    (1 - x) ^ u ≤ 1 - u * x := by
  have h := Real.geom_mean_le_arith_mean2_weighted
    (w₁ := 1 - u) (w₂ := u) (p₁ := 1) (p₂ := 1 - x)
    (by linarith) hu0 (by norm_num) (by linarith) (by ring)
  simp only [Real.one_rpow, one_mul, mul_one] at h
  nlinarith

/-- Lower comparison of the positive generating-function Euler factor with a squarefree factor. -/
lemma positive_euler_factor_lower {u x : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x < 1) : (1 + x) ^ u ≤ (1 - u * x)⁻¹ := by
  have hux : u * x < 1 := (mul_le_mul_of_nonneg_right hu1 hx0).trans_lt (by simpa using hx1)
  have hden : 0 < 1 - u * x := by linarith
  calc
    (1 + x) ^ u ≤ 1 + u * x := rpow_one_add_le_linear hu0 hu1 hx0
    _ ≤ (1 - u * x)⁻¹ := by
      rw [← one_div, le_div_iff₀ hden]
      nlinarith [sq_nonneg (u * x)]

/-- Upper comparison with the u-th power of the ordinary Euler factor. -/
lemma positive_euler_factor_upper {u x : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hx1 : x < 1) : (1 - u * x)⁻¹ ≤ ((1 - x) ^ u)⁻¹ := by
  have hp : 0 < (1 - x) ^ u := Real.rpow_pos_of_pos (by linarith) _
  have hle := rpow_one_sub_le_linear hu0 hu1 hx1
  simpa only [one_div] using one_div_le_one_div_of_le hp hle

lemma complex_norm_sq_interpolation (u : ℝ) (z : ℂ) :
    ‖1 - (u : ℂ) * z‖ ^ 2 =
      (1 - u) + u * ‖1 - z‖ ^ 2 - u * (1 - u) * ‖z‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- A uniform twisted-factor bound needing no choice of a complex logarithm.
The correction factors have a convergent Euler product when |z_p| ≤ 1/p. -/
lemma complex_euler_factor_lower {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    (‖1 - z‖ ^ 2) ^ u * (1 - ‖z‖ ^ 2) ≤ ‖1 - (u : ℂ) * z‖ ^ 2 := by
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hnorm : (1 : ℝ) - ‖z‖ ≤ ‖1 - z‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) z
  have hnorm0 : 0 ≤ ‖1 - z‖ := norm_nonneg _
  have hA : (1 / 4 : ℝ) ≤ ‖1 - z‖ ^ 2 := by nlinarith
  have hS : (1 / 4 : ℝ) ≤ (1 - u) + u * ‖1 - z‖ ^ 2 := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hA)]
  have hvar : u * (1 - u) ≤ (1 / 4 : ℝ) := by nlinarith [sq_nonneg (u - 1 / 2)]
  have hcorrection : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith
  have hmean := Real.geom_mean_le_arith_mean2_weighted
    (w₁ := 1 - u) (w₂ := u) (p₁ := 1) (p₂ := ‖1 - z‖ ^ 2)
    (by linarith) hu0 (by norm_num) (sq_nonneg _) (by ring)
  simp only [Real.one_rpow, one_mul, mul_one] at hmean
  have hproduct := mul_le_mul_of_nonneg_right hmean hcorrection
  have hvariance := mul_le_mul_of_nonneg_right (hvar.trans hS) (sq_nonneg ‖z‖)
  rw [complex_norm_sq_interpolation]
  nlinarith [hproduct, hvariance]

/-- The inverse-factor estimate in the form used for finite Euler products. -/
lemma complex_inverse_euler_factor_upper {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖(1 - (u : ℂ) * z)⁻¹‖ ^ 2 ≤
      ‖(1 - z)⁻¹‖ ^ (2 * u) * (1 - ‖z‖ ^ 2)⁻¹ := by
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hnorm : (1 : ℝ) - ‖z‖ ≤ ‖1 - z‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) z
  have hbase : 0 < ‖1 - z‖ := by linarith
  have hcor : 0 < 1 - ‖z‖ ^ 2 := by nlinarith
  have hpow : 0 < (‖1 - z‖ ^ 2) ^ u :=
    Real.rpow_pos_of_pos (pow_pos hbase _) _
  have hi := one_div_le_one_div_of_le (mul_pos hpow hcor)
    (complex_euler_factor_lower hu0 hu1 hz)
  rw [norm_inv, inv_pow]
  simp only [one_div, mul_inv_rev] at hi
  calc
    (‖1 - (u : ℂ) * z‖ ^ 2)⁻¹ ≤
        (1 - ‖z‖ ^ 2)⁻¹ * ((‖1 - z‖ ^ 2) ^ u)⁻¹ := hi
    _ = ‖(1 - z)⁻¹‖ ^ (2 * u) * (1 - ‖z‖ ^ 2)⁻¹ := by
      rw [norm_inv, Real.inv_rpow (norm_nonneg _), Real.rpow_mul (norm_nonneg _), Real.rpow_two]
      ring

/-- A finite product version; all correction factors stay positive. -/
lemma complex_finite_euler_product_upper {ι : Type*} (S : Finset ι)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (z : ι → ℂ)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 1 / 2) :
    ‖∏ i ∈ S, (1 - (u : ℂ) * z i)⁻¹‖ ^ 2 ≤
      ‖∏ i ∈ S, (1 - z i)⁻¹‖ ^ (2 * u) * ∏ i ∈ S, (1 - ‖z i‖ ^ 2)⁻¹ := by
  have h := Finset.prod_le_prod
    (fun i hi => sq_nonneg ‖(1 - (u : ℂ) * z i)⁻¹‖)
    (fun i hi => complex_inverse_euler_factor_upper hu0 hu1 (hz i hi))
  simpa only [Finset.prod_mul_distrib, Finset.prod_pow, Real.finset_prod_rpow S
    (fun i => ‖(1 - z i)⁻¹‖) (fun _ _ => norm_nonneg _) (2 * u), norm_prod] using h

/-- Passing the finite comparison to convergent products does not need nonvanishing of L.
The rpow exponent is nonnegative, so the limiting norm may even be zero. -/
lemma complex_euler_product_upper {ι : Type*} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1 / 2) {F L : ℂ} {Q : ℝ}
    (hF : HasProd (fun i => (1 - (u : ℂ) * z i)⁻¹) F)
    (hL : HasProd (fun i => (1 - z i)⁻¹) L)
    (hQ : HasProd (fun i => (1 - ‖z i‖ ^ 2)⁻¹) Q) :
    ‖F‖ ^ 2 ≤ ‖L‖ ^ (2 * u) * Q := by
  change Filter.Tendsto (fun S : Finset ι => ∏ i ∈ S, (1 - (u : ℂ) * z i)⁻¹)
    Filter.atTop (nhds F) at hF
  change Filter.Tendsto (fun S : Finset ι => ∏ i ∈ S, (1 - z i)⁻¹)
    Filter.atTop (nhds L) at hL
  change Filter.Tendsto (fun S : Finset ι => ∏ i ∈ S, (1 - ‖z i‖ ^ 2)⁻¹)
    Filter.atTop (nhds Q) at hQ
  exact le_of_tendsto_of_tendsto (hF.norm.pow 2)
    ((hL.norm.rpow_const (Or.inr (by positivity : (0 : ℝ) ≤ 2 * u))).mul hQ)
    (Filter.Eventually.of_forall (fun S => complex_finite_euler_product_upper S hu0 hu1 z
      (fun i _ => hz i)))

end Erdos143
