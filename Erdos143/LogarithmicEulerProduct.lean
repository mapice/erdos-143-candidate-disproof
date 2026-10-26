import Erdos143.GeneratingEulerProducts

noncomputable section
open Complex
open scoped BigOperators Topology LSeries.notation

namespace Erdos143

/-- The absolutely convergent sum of local logarithmic Euler corrections. -/
def logarithmicEulerRemainder {ι : Type*} (z : ι → ℂ) (u : ℝ) : ℂ :=
  ∑' i, (-Complex.log (1 - (u : ℂ) * z i) + (u : ℂ) * Complex.log (1 - z i))

lemma logarithmicEulerRemainder_summable {ι : Type*} {z : ι → ℂ}
    (hz : Summable z) (u : ℝ) :
    Summable (fun i => -Complex.log (1 - (u : ℂ) * z i) +
      (u : ℂ) * Complex.log (1 - z i)) :=
  ((hz.mul_left (u : ℂ)).clog_one_sub.neg).add (hz.clog_one_sub.mul_left (u : ℂ))

/-- An identity between real logarithms of norms, without a logarithm of the global product. -/
lemma logarithmic_euler_identity {ι : Type*} {z : ι → ℂ}
    (hz : Summable z) (u : ℝ) {F Z : ℂ}
    (hF : Complex.exp (∑' i, -Complex.log (1 - (u : ℂ) * z i)) = F)
    (hZ : Complex.exp (∑' i, -Complex.log (1 - z i)) = Z) :
    Real.log ‖F‖ = u * Real.log ‖Z‖ + (logarithmicEulerRemainder z u).re := by
  have hsum := (hz.mul_left (u : ℂ)).clog_one_sub.neg
  have hsumZ := hz.clog_one_sub.neg
  have hR : logarithmicEulerRemainder z u =
      (∑' i, -Complex.log (1 - (u : ℂ) * z i)) -
        (u : ℂ) * (∑' i, -Complex.log (1 - z i)) := by
    unfold logarithmicEulerRemainder
    rw [hsum.tsum_add (hz.clog_one_sub.mul_left (u : ℂ)), tsum_mul_left,
      tsum_neg]
    simp only [tsum_neg, mul_neg]
    ring
  rw [← hF, ← hZ, Complex.norm_exp, Complex.norm_exp, Real.log_exp, Real.log_exp, hR]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

/-- The prime factors of a Dirichlet series are absolutely summable in Re(s)>1. -/
lemma dirichlet_prime_factors_summable {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => χ p * (p : ℂ) ^ (-s)) := by
  have h := (summable_dirichletSummand χ hs).of_norm.subtype {p : ℕ | p.Prime}
  simpa only [Set.coe_setOf, Set.mem_setOf_eq, Function.comp_apply, dirichletSummandHom] using h

/-- The revised paper's logarithmic identity for the actual generating series. -/
lemma generatingValue_eq_exp_log {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (∑' p : Nat.Primes,
      -Complex.log (1 - (u : ℂ) * (χ p * (p : ℂ) ^ (-s)))) =
      generatingValue χ (u : ℂ) s := by
  have hu : ‖(u : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0] using hu1
  have h := EulerProduct.exp_tsum_primes_log_eq_tsum
    (generatingSummand_norm_summable χ hu hs)
  simpa only [generatingSummand_at_prime,
    ← generatingValue_eq_tsum χ (u : ℂ) (ne_zero_of_one_lt_re hs)] using h

lemma generatingValue_ne_zero_logarithmic {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    generatingValue χ (u : ℂ) s ≠ 0 := by
  rw [← generatingValue_eq_exp_log χ hu0 hu1 hs]
  exact Complex.exp_ne_zero _

lemma LSeries_ne_zero_logarithmic {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) : L ↗χ s ≠ 0 := by
  rw [← χ.LSeries_eulerProduct_exp_log hs]
  exact Complex.exp_ne_zero _

/-- Taking real logarithms does not require nonvanishing at the boundary s=1. -/
lemma generatingValue_logarithmic_identity {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Real.log ‖generatingValue χ (u : ℂ) s‖ =
      u * Real.log ‖L ↗χ s‖ +
        (logarithmicEulerRemainder (fun p : Nat.Primes => χ p * (p : ℂ) ^ (-s)) u).re := by
  apply logarithmic_euler_identity (dirichlet_prime_factors_summable χ hs) u
  · exact generatingValue_eq_exp_log χ hu0 hu1 hs
  · exact χ.LSeries_eulerProduct_exp_log hs

end Erdos143
