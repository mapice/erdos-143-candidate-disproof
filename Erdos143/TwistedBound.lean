import Erdos143.GeneratingEulerProducts
import Erdos143.EulerFactorBounds
import Erdos143.CorrectionProducts
import Erdos143.AnalyticInputs

noncomputable section
open Complex
open scoped Topology LSeries.notation

namespace Erdos143

lemma dirichlet_prime_factor_norm_le_reciprocal {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    ‖dirichletSummandHom χ (ne_zero_of_one_lt_re hs) p‖ ≤ (p : ℝ)⁻¹ := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast p.property.one_lt.le
  change ‖χ p * (p : ℂ) ^ (-s)‖ ≤ _
  rw [norm_mul]
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_nonneg (by positivity)
      (re_neg_ne_zero_of_one_lt_re hs), neg_re]
  rw [hnorm]
  calc
    ‖χ p‖ * (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-s.re) :=
      mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _) (χ.norm_le_one p)
    _ ≤ (p : ℝ)⁻¹ := by
      have h := Real.rpow_le_rpow_of_exponent_le hp (show -s.re ≤ (-1 : ℝ) by linarith)
      simpa only [Real.rpow_neg_one] using h

/-- Uniform generating-function norm bound from a genuine Euler product and a telescoping
quadratic correction. No complex logarithm or L(1,χ) nonvanishing is assumed. -/
lemma generating_norm_sq_le_LSeries {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    ‖∑' n, generatingSummandHom χ (u : ℂ) (ne_zero_of_one_lt_re hs) n‖ ^ 2 ≤
      2 * ‖L ↗χ s‖ ^ (2 * u) := by
  have hu : ‖(u : ℂ)‖ ≤ 1 := by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0] using hu1
  let z : Nat.Primes → ℂ := fun p => dirichletSummandHom χ (ne_zero_of_one_lt_re hs) p
  have hz : ∀ p, ‖z p‖ ≤ (p : ℝ)⁻¹ := dirichlet_prime_factor_norm_le_reciprocal χ hs
  have hhalf : ∀ p, ‖z p‖ ≤ 1 / 2 := fun p => (hz p).trans (prime_reciprocal_le_half p)
  have hF := generating_eulerProduct_hasProd χ hu hs
  have hL := χ.LSeries_eulerProduct_hasProd hs
  have hFp : HasProd (fun p : Nat.Primes => (1 - (u : ℂ) * z p)⁻¹)
      (∑' n, generatingSummandHom χ (u : ℂ) (ne_zero_of_one_lt_re hs) n) := by
    simpa [generatingSummand_at_prime, z, dirichletSummandHom] using hF
  have hLp : HasProd (fun p : Nat.Primes => (1 - z p)⁻¹) (L ↗χ s) := by
    simpa [z, dirichletSummandHom] using hL
  change Filter.Tendsto (fun S : Finset Nat.Primes => ∏ p ∈ S, (1 - (u : ℂ) * z p)⁻¹)
    Filter.atTop (nhds _) at hFp
  change Filter.Tendsto (fun S : Finset Nat.Primes => ∏ p ∈ S, (1 - z p)⁻¹)
    Filter.atTop (nhds _) at hLp
  apply le_of_tendsto_of_tendsto (hFp.norm.pow 2)
    ((hLp.norm.rpow_const (Or.inr (by positivity : (0 : ℝ) ≤ 2 * u))).const_mul 2)
  apply Filter.Eventually.of_forall
  intro S
  have hfinite := complex_finite_euler_product_upper S hu0 hu1 z (fun p _ => hhalf p)
  have hcor := prime_correction_product_le_two S z (fun p _ => hz p)
  have hmul := mul_le_mul_of_nonneg_left hcor
    (Real.rpow_nonneg (norm_nonneg (∏ p ∈ S, (1 - z p)⁻¹)) (2 * u))
  exact hfinite.trans (by nlinarith [hmul])

lemma generatingValue_norm_sq_le_LSeries {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    ‖generatingValue χ (u : ℂ) s‖ ^ 2 ≤ 2 * ‖L ↗χ s‖ ^ (2 * u) := by
  rw [generatingValue_eq_tsum χ (u : ℂ) (ne_zero_of_one_lt_re hs)]
  exact generating_norm_sq_le_LSeries χ hu0 hu1 hs

lemma generatingValue_norm_le_two_rpow_LSeries {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    ‖generatingValue χ (u : ℂ) s‖ ≤ 2 * ‖L ↗χ s‖ ^ u := by
  have h := generatingValue_norm_sq_le_LSeries χ hu0 hu1 hs
  have hid : ‖L ↗χ s‖ ^ (2 * u) = (‖L ↗χ s‖ ^ u) ^ 2 := by
    rw [mul_comm (2 : ℝ) u, Real.rpow_mul (norm_nonneg _), Real.rpow_two]
  rw [hid] at h
  nlinarith [norm_nonneg (generatingValue χ (u : ℂ) s), Real.rpow_nonneg (norm_nonneg (L ↗χ s)) u]

/-- The uniform bound near s=1 needed for the Abel-average method. It is proved from
continuity of the nonprincipal L-function and does not use nonvanishing at 1. -/
lemma nonprincipal_generatingValue_bounded {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖generatingValue χ (u : ℂ) (1 + (t : ℂ))‖ ≤ C := by
  have hcont : Continuous (fun t : ℝ => χ.LFunction (1 + (t : ℂ))) :=
    (nonprincipal_LFunction_continuous χ hχ).comp (continuous_const.add Complex.continuous_ofReal)
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hcont.continuousOn
  let K : ℝ := max 1 B
  have hK : 1 ≤ K := le_max_left _ _
  refine ⟨2 * K, by positivity, ?_⟩
  intro u hu0 hu1 t ht0 ht1
  have hs : 1 < (1 + (t : ℂ)).re := by simpa using ht0
  have hL : ‖L ↗χ (1 + (t : ℂ))‖ ≤ K := by
    rw [← χ.LFunction_eq_LSeries hs]
    exact (hB t ⟨ht0.le, ht1⟩).trans (le_max_right _ _)
  have he : (0 : ℝ) ≤ 2 * u := by positivity
  have hpow : ‖L ↗χ (1 + (t : ℂ))‖ ^ (2 * u) ≤ K ^ 2 := by
    calc
      _ ≤ K ^ (2 * u) := Real.rpow_le_rpow (norm_nonneg _) hL he
      _ ≤ K ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK (by linarith)
      _ = K ^ 2 := Real.rpow_two _
  have hnorm := generatingValue_norm_sq_le_LSeries χ hu0 hu1 hs
  nlinarith [norm_nonneg (generatingValue χ (u : ℂ) (1 + (t : ℂ)))]

end Erdos143
