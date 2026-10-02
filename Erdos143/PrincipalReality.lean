import Erdos143.PrincipalBound

noncomputable section
open Complex
open scoped ArithmeticFunction.Omega

namespace Erdos143

def principalGeneratingTerm (N : ℕ) (u s : ℝ) (n : ℕ) : ℝ := by
  classical
  exact if IsUnit (n : ZMod N) then u ^ Ω n * (n : ℝ) ^ (-s) else 0

lemma principalGeneratingTerm_nonneg {N : ℕ} {u s : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    0 ≤ principalGeneratingTerm N u s n := by
  unfold principalGeneratingTerm
  split_ifs <;> positivity

lemma principalGeneratingTerm_one (N : ℕ) (u s : ℝ) : principalGeneratingTerm N u s 1 = 1 := by
  simp [principalGeneratingTerm]

lemma principalGeneratingTerm_cast {N : ℕ} {u s : ℝ} (hs : 1 < s) (n : ℕ) :
    generatingSummandHom (1 : DirichletCharacter ℂ N) (u : ℂ)
      (ne_zero_of_one_lt_re (show 1 < (s : ℂ).re by simpa using hs)) n =
      (principalGeneratingTerm N u s n : ℂ) := by
  by_cases hn : n = 0
  · have hs0 : -s ≠ 0 := by linarith
    simp [hn, principalGeneratingTerm, Real.zero_rpow hs0]
  · change omegaWeightHom (u : ℂ) n * ((1 : DirichletCharacter ℂ N) n * (n : ℂ) ^ (-(s : ℂ))) = _
    rw [omegaWeightHom_apply hn]
    by_cases hunit : IsUnit (n : ZMod N)
    · rw [MulChar.one_apply hunit, one_mul]
      simp only [principalGeneratingTerm, if_pos hunit, ofReal_mul, ofReal_pow,
        ofReal_cpow (Nat.cast_nonneg n), ofReal_neg, ofReal_natCast]
    · rw [MulChar.map_nonunit (1 : DirichletCharacter ℂ N) hunit, zero_mul, mul_zero]
      simp [principalGeneratingTerm, hunit]

lemma principalGeneratingTerm_summable {N : ℕ} {u s : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hs : 1 < s) : Summable (principalGeneratingTerm N u s) := by
  have hu : ‖(u : ℂ)‖ ≤ 1 := by rw [Complex.norm_of_nonneg hu0]; exact hu1
  have h := generatingSummand_norm_summable (1 : DirichletCharacter ℂ N) hu
    (show 1 < (s : ℂ).re by simpa using hs)
  simpa only [principalGeneratingTerm_cast hs, Complex.norm_of_nonneg (principalGeneratingTerm_nonneg hu0 _)] using h

lemma principalGeneratingValue_eq_real_sum {N : ℕ} {u s : ℝ} (hs : 1 < s) :
    generatingValue (1 : DirichletCharacter ℂ N) (u : ℂ) (s : ℂ) =
      (∑' n, principalGeneratingTerm N u s n : ℝ) := by
  rw [generatingValue_eq_tsum _ _ (ne_zero_of_one_lt_re (show 1 < (s : ℂ).re by simpa using hs))]
  simp only [principalGeneratingTerm_cast hs, Complex.ofReal_tsum]

lemma principalGeneratingValue_norm_eq_sum {N : ℕ} {u s : ℝ} (hu0 : 0 ≤ u) (hs : 1 < s) :
    ‖generatingValue (1 : DirichletCharacter ℂ N) (u : ℂ) (s : ℂ)‖ =
      ∑' n, principalGeneratingTerm N u s n := by
  rw [principalGeneratingValue_eq_real_sum hs]
  exact Complex.norm_of_nonneg (tsum_nonneg (principalGeneratingTerm_nonneg hu0))

lemma principalGeneratingValue_norm_one_le {N : ℕ} {u s : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hs : 1 < s) :
    1 ≤ ‖generatingValue (1 : DirichletCharacter ℂ N) (u : ℂ) (s : ℂ)‖ := by
  rw [principalGeneratingValue_norm_eq_sum hu0 hs]
  have h := (principalGeneratingTerm_summable (N := N) hu0 hu1 hs).le_tsum 1
    (fun n _ => principalGeneratingTerm_nonneg hu0 n)
  simpa only [principalGeneratingTerm_one] using h

end Erdos143
