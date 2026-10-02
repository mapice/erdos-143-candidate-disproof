import Erdos143.EulerFactorBounds
import Erdos143.CorrectionProducts

noncomputable section
open scoped BigOperators Topology

namespace Erdos143

lemma positive_finite_euler_product_lower (S : Finset Nat.Primes) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (x : Nat.Primes → ℝ)
    (hx0 : ∀ p ∈ S, 0 ≤ x p) (hx : ∀ p ∈ S, x p ≤ (p : ℝ)⁻¹) :
    ((∏ p ∈ S, (1 - x p)⁻¹) / 2) ^ u ≤ ∏ p ∈ S, (1 - u * x p)⁻¹ := by
  have hhalf : ∀ p ∈ S, x p ≤ 1 / 2 := fun p hp => (hx p hp).trans (prime_reciprocal_le_half p)
  have hcor : (∏ p ∈ S, (1 - (x p) ^ 2)⁻¹) ≤ 2 := by
    have h := prime_correction_product_le_two S (fun p => (x p : ℂ)) (fun p hp => by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hx0 p hp)] using hx p hp)
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using h
  have hidentity : (∏ p ∈ S, (1 + x p)) * (∏ p ∈ S, (1 - (x p) ^ 2)⁻¹) =
      ∏ p ∈ S, (1 - x p)⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp0 := hx0 p hp
    have hp1 := hhalf p hp
    have h1 : 1 - x p ≠ 0 := by linarith
    have h2 : 1 - (x p) ^ 2 ≠ 0 := by nlinarith
    field_simp
    ring
  have hA : 0 ≤ ∏ p ∈ S, (1 + x p) := Finset.prod_nonneg (fun p hp => by linarith [hx0 p hp])
  have hZ : 0 ≤ ∏ p ∈ S, (1 - x p)⁻¹ := Finset.prod_nonneg (fun p hp => by
    apply inv_nonneg.mpr
    linarith [hhalf p hp])
  have hcompare : (∏ p ∈ S, (1 - x p)⁻¹) / 2 ≤ ∏ p ∈ S, (1 + x p) := by
    have hmul := mul_le_mul_of_nonneg_left hcor hA
    rw [hidentity] at hmul
    linarith
  calc
    _ ≤ (∏ p ∈ S, (1 + x p)) ^ u := Real.rpow_le_rpow (by positivity) hcompare hu0
    _ = ∏ p ∈ S, (1 + x p) ^ u :=
      (Real.finset_prod_rpow S (fun p => 1 + x p) (fun p hp => by linarith [hx0 p hp]) u).symm
    _ ≤ _ := Finset.prod_le_prod (fun p hp => Real.rpow_nonneg (by linarith [hx0 p hp]) _)
      (fun p hp => positive_euler_factor_lower hu0 hu1 (hx0 p hp) (by linarith [hhalf p hp]))

lemma positive_euler_product_lower {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (x : Nat.Primes → ℝ) (hx0 : ∀ p, 0 ≤ x p) (hx : ∀ p, x p ≤ (p : ℝ)⁻¹)
    {F Z : ℝ} (hF : HasProd (fun p => (1 - u * x p)⁻¹) F)
    (hZ : HasProd (fun p => (1 - x p)⁻¹) Z) : (Z / 2) ^ u ≤ F := by
  change Filter.Tendsto (fun S : Finset Nat.Primes => ∏ p ∈ S, (1 - u * x p)⁻¹)
    Filter.atTop (nhds F) at hF
  change Filter.Tendsto (fun S : Finset Nat.Primes => ∏ p ∈ S, (1 - x p)⁻¹)
    Filter.atTop (nhds Z) at hZ
  exact le_of_tendsto_of_tendsto ((hZ.div_const 2).rpow_const (Or.inr hu0)) hF
    (Filter.Eventually.of_forall (fun S => positive_finite_euler_product_lower S hu0 hu1 x
      (fun p _ => hx0 p) (fun p _ => hx p)))

end Erdos143
