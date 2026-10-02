import Erdos143.Definitions
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

noncomputable section
open scoped ArithmeticFunction.Omega
open Complex

namespace Erdos143

/-- The completely multiplicative Ω weight, with the required zero convention. -/
def omegaWeightHom (u : ℂ) : ℕ →*₀ ℂ where
  toFun n := if n = 0 then 0 else u ^ Ω n
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    simp [hm, hn, mul_ne_zero hm hn, ArithmeticFunction.cardFactors_mul hm hn, pow_add]

lemma omegaWeightHom_apply {u : ℂ} {n : ℕ} (hn : n ≠ 0) :
    omegaWeightHom u n = u ^ Ω n := by simp [omegaWeightHom, hn]

lemma omegaWeightHom_norm_le_one {u : ℂ} (hu : ‖u‖ ≤ 1) (n : ℕ) :
    ‖omegaWeightHom u n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  rw [omegaWeightHom_apply hn, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) hu

/-- Completely multiplicative twisted generating summand. -/
def generatingSummandHom {L : ℕ} (χ : DirichletCharacter ℂ L) (u : ℂ)
    {s : ℂ} (hs : s ≠ 0) : ℕ →*₀ ℂ where
  toFun n := omegaWeightHom u n * dirichletSummandHom χ hs n
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by simp only [map_mul]; ring

lemma generatingSummand_norm_summable {L : ℕ} (χ : DirichletCharacter ℂ L)
    {u s : ℂ} (hu : ‖u‖ ≤ 1) (hs : 1 < s.re) :
    Summable (fun n => ‖generatingSummandHom χ u (ne_zero_of_one_lt_re hs) n‖) := by
  apply (summable_dirichletSummand χ hs).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  change ‖omegaWeightHom u n * dirichletSummandHom χ _ n‖ ≤ _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (omegaWeightHom_norm_le_one hu n)

/-- Euler product for the Ω generating series in the full absolute-convergence region needed
by the real Abel-parameter route. -/
lemma generating_eulerProduct_hasProd {L : ℕ} (χ : DirichletCharacter ℂ L)
    {u s : ℂ} (hu : ‖u‖ ≤ 1) (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes =>
      (1 - generatingSummandHom χ u (ne_zero_of_one_lt_re hs) p)⁻¹)
      (∑' n, generatingSummandHom χ u (ne_zero_of_one_lt_re hs) n) :=
  EulerProduct.eulerProduct_completely_multiplicative_hasProd
    (generatingSummand_norm_summable χ hu hs)

lemma generatingSummand_at_prime {L : ℕ} (χ : DirichletCharacter ℂ L)
    {u s : ℂ} (hs : s ≠ 0) (p : Nat.Primes) :
    generatingSummandHom χ u hs p = u * (χ p * (p : ℂ) ^ (-s)) := by
  simp [generatingSummandHom, omegaWeightHom, p.property.ne_zero,
    ArithmeticFunction.cardFactors_apply_prime p.property, dirichletSummandHom]

/-- A parameter-independent presentation of the generating series. -/
def generatingValue {L : ℕ} (χ : DirichletCharacter ℂ L) (u s : ℂ) : ℂ :=
  ∑' n : ℕ, omegaWeightHom u n * (χ n * (n : ℂ) ^ (-s))

lemma generatingValue_eq_tsum {L : ℕ} (χ : DirichletCharacter ℂ L) (u : ℂ)
    {s : ℂ} (hs : s ≠ 0) :
    generatingValue χ u s = ∑' n, generatingSummandHom χ u hs n := rfl

end Erdos143
