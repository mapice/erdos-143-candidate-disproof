import Erdos143.PrincipalReality
import Erdos143.GeneratingTail

noncomputable section
open Complex
open scoped ArithmeticFunction.Omega

namespace Erdos143

lemma principalGeneratingTerm_mod_one (u s : ℝ) (n : ℕ) :
    principalGeneratingTerm 1 u s n = u ^ Ω n * (n : ℝ) ^ (-s) := by
  simp only [principalGeneratingTerm, isUnit_of_subsingleton, if_true]

lemma generatingSummand_norm_le_principalTerm {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u s : ℝ} (hu0 : 0 ≤ u) (hs : 1 < s) (n : ℕ) :
    ‖generatingSummandHom χ (u : ℂ)
      (ne_zero_of_one_lt_re (show 1 < (s : ℂ).re by simpa using hs)) n‖ ≤
      principalGeneratingTerm 1 u s n := by
  rw [principalGeneratingTerm_mod_one]
  by_cases hn : n = 0
  · have hs0 : -s ≠ 0 := by linarith
    simp [hn, Real.zero_rpow hs0]
  · have hsC : 1 < (s : ℂ).re := by simpa using hs
    change ‖omegaWeightHom (u : ℂ) n * (χ n * (n : ℂ) ^ (-(s : ℂ)))‖ ≤ _
    rw [omegaWeightHom_apply hn, norm_mul, norm_mul, norm_pow, Complex.norm_of_nonneg hu0]
    have hnorm : ‖(n : ℂ) ^ (-(s : ℂ))‖ = (n : ℝ) ^ (-s) := by
      rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n)
        (re_neg_ne_zero_of_one_lt_re hsC), neg_re, ofReal_re]
    rw [hnorm]
    have hχ := mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) (-s)) (χ.norm_le_one n)
    exact mul_le_mul_of_nonneg_left hχ (pow_nonneg hu0 _)

lemma generatingValue_norm_le_global {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u s : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hs : 1 < s) :
    ‖generatingValue χ (u : ℂ) (s : ℂ)‖ ≤
      ‖generatingValue (1 : DirichletCharacter ℂ 1) (u : ℂ) (s : ℂ)‖ := by
  have hsC : 1 < (s : ℂ).re := by simpa using hs
  have hu : ‖(u : ℂ)‖ ≤ 1 := by rw [Complex.norm_of_nonneg hu0]; exact hu1
  have hsum := generatingSummand_norm_summable χ hu hsC
  rw [generatingValue_eq_tsum χ _ (ne_zero_of_one_lt_re hsC),
    principalGeneratingValue_norm_eq_sum hu0 hs]
  exact (norm_tsum_le_tsum_norm hsum).trans (hsum.tsum_le_tsum
    (generatingSummand_norm_le_principalTerm χ hu0 hs)
    (principalGeneratingTerm_summable (N := 1) hu0 hu1 hs))

end Erdos143
