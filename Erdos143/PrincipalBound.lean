import Erdos143.PositiveEulerBound
import Erdos143.TwistedBound

noncomputable section
open Complex
open scoped BigOperators Topology LSeries.notation

namespace Erdos143

lemma principal_prime_factor_real {N : ℕ} {s : ℝ} (hs : 1 < s) (p : Nat.Primes) :
    dirichletSummandHom (1 : DirichletCharacter ℂ N)
      (ne_zero_of_one_lt_re (show 1 < (s : ℂ).re by simpa using hs)) p =
    (‖dirichletSummandHom (1 : DirichletCharacter ℂ N)
      (ne_zero_of_one_lt_re (show 1 < (s : ℂ).re by simpa using hs)) p‖ : ℂ) := by
  change (1 : DirichletCharacter ℂ N) p * (p : ℂ) ^ (-(s : ℂ)) =
    (‖(1 : DirichletCharacter ℂ N) p * (p : ℂ) ^ (-(s : ℂ))‖ : ℂ)
  by_cases hunit : IsUnit ((p : ℕ) : ZMod N)
  · rw [MulChar.one_apply hunit, one_mul]
    have hpow : (p : ℂ) ^ (-(s : ℂ)) = Complex.ofReal ((p : ℝ) ^ (-s)) := by
      rw [ofReal_cpow (by positivity), ofReal_neg, ofReal_natCast]
    rw [hpow, Complex.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  · rw [MulChar.map_nonunit (1 : DirichletCharacter ℂ N) hunit, zero_mul]
    simp

/-- A principal generating series is at least the u-th power of half its ordinary L-series.
This suffices for a positive Abel-average residue after integration near s=1. -/
lemma principal_generatingValue_lower {N : ℕ} {u s : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hs : 1 < s) :
    (‖L ↗(1 : DirichletCharacter ℂ N) (s : ℂ)‖ / 2) ^ u ≤
      ‖generatingValue (1 : DirichletCharacter ℂ N) (u : ℂ) (s : ℂ)‖ := by
  let χ : DirichletCharacter ℂ N := 1
  have hsC : 1 < (s : ℂ).re := by simpa using hs
  let z : Nat.Primes → ℂ := fun p => dirichletSummandHom χ (ne_zero_of_one_lt_re hsC) p
  let x : Nat.Primes → ℝ := fun p => ‖z p‖
  have hx0 : ∀ p, 0 ≤ x p := fun p => norm_nonneg _
  have hx : ∀ p, x p ≤ (p : ℝ)⁻¹ := dirichlet_prime_factor_norm_le_reciprocal χ hsC
  have hhalf : ∀ p, x p ≤ 1 / 2 := fun p => (hx p).trans (prime_reciprocal_le_half p)
  have hreal : ∀ p, z p = (x p : ℂ) := principal_prime_factor_real hs
  have hu : ‖(u : ℂ)‖ ≤ 1 := by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0] using hu1
  have hF : HasProd (fun p : Nat.Primes => (1 - (u : ℂ) * z p)⁻¹)
      (generatingValue χ (u : ℂ) (s : ℂ)) := by
    simpa [generatingValue_eq_tsum χ (u : ℂ) (ne_zero_of_one_lt_re hsC),
      generatingSummand_at_prime, z, dirichletSummandHom] using
      generating_eulerProduct_hasProd χ hu hsC
  have hZ : HasProd (fun p : Nat.Primes => (1 - z p)⁻¹) (L ↗χ (s : ℂ)) := by
    simpa [z, dirichletSummandHom] using χ.LSeries_eulerProduct_hasProd hsC
  have hfactors (v : ℝ) (_hv0 : 0 ≤ v) (hv1 : v ≤ 1) (p : Nat.Primes) :
      ‖(1 - (v : ℂ) * z p)⁻¹‖ = (1 - v * x p)⁻¹ := by
    have hp : 0 ≤ 1 - v * x p := by
      have hmul := mul_le_mul_of_nonneg_right hv1 (hx0 p)
      linarith [hhalf p]
    rw [hreal]
    have heq : (1 - (v : ℂ) * (x p : ℂ))⁻¹ = (((1 - v * x p)⁻¹ : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [heq, Complex.norm_of_nonneg (inv_nonneg.mpr hp)]
  have hFnorm : HasProd (fun p => (1 - u * x p)⁻¹)
      ‖generatingValue χ (u : ℂ) (s : ℂ)‖ := by
    change Filter.Tendsto (fun S : Finset Nat.Primes => ∏ p ∈ S, (1 - (u : ℂ) * z p)⁻¹)
      Filter.atTop (nhds _) at hF
    simpa only [norm_prod, hfactors u hu0 hu1] using hF.norm
  have hZnorm : HasProd (fun p => (1 - x p)⁻¹) ‖L ↗χ (s : ℂ)‖ := by
    change Filter.Tendsto (fun S : Finset Nat.Primes => ∏ p ∈ S, (1 - z p)⁻¹)
      Filter.atTop (nhds _) at hZ
    have hone (p : Nat.Primes) : ‖(1 - z p)⁻¹‖ = (1 - x p)⁻¹ := by
      simpa using hfactors 1 (by norm_num) (by norm_num) p
    simpa only [norm_prod, hone] using hZ.norm
  exact positive_euler_product_lower hu0 hu1 x hx0 hx hFnorm hZnorm

end Erdos143
