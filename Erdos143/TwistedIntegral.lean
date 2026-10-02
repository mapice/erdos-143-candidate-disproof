import Erdos143.WeightedIntegrability

noncomputable section
open MeasureTheory Set Complex
open scoped ArithmeticFunction.Omega

namespace Erdos143

def complexGeneratingTailTerm {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℝ)
    (n : ℕ) (t : ℝ) : ℂ := χ (n + 2) * (realGeneratingTailTerm u n t : ℂ)

def weightedCharacterTerm {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℝ) (n : ℕ) : ℂ :=
  χ (n + 2) * ((u ^ Ω (n + 2) / (((n : ℝ) + 2) * Real.log ((n : ℝ) + 2)) : ℝ) : ℂ)

lemma complexGeneratingTailTerm_integrable {N : ℕ} (χ : DirichletCharacter ℂ N)
    (u : ℝ) (n : ℕ) : IntegrableOn (complexGeneratingTailTerm χ u n) (Ioi 0) :=
  (realGeneratingTailTerm_integrable u n).ofReal.const_mul _

lemma integral_complexGeneratingTailTerm {N : ℕ} (χ : DirichletCharacter ℂ N)
    (u : ℝ) (n : ℕ) :
    (∫ t : ℝ in Ioi 0, complexGeneratingTailTerm χ u n t) = weightedCharacterTerm χ u n := by
  unfold complexGeneratingTailTerm weightedCharacterTerm
  rw [integral_const_mul, integral_complex_ofReal, integral_realGeneratingTailTerm]

lemma complexGeneratingTailTerm_norm_integral_le {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    (∫ t : ℝ in Ioi 0, ‖complexGeneratingTailTerm χ u n t‖) ≤
      u ^ Ω (n + 2) / (((n : ℝ) + 2) * Real.log ((n : ℝ) + 2)) := by
  simp only [complexGeneratingTailTerm, norm_mul,
    Complex.norm_of_nonneg (realGeneratingTailTerm_nonneg hu _ _)]
  rw [integral_const_mul, integral_realGeneratingTailTerm]
  have hw : 0 ≤ u ^ Ω (n + 2) / (((n : ℝ) + 2) * Real.log ((n : ℝ) + 2)) := by
    have hlog : 0 < Real.log ((n : ℝ) + 2) := Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])
    positivity
  exact mul_le_of_le_one_left hw (χ.norm_le_one (n + 2))

lemma complexGeneratingTailTerm_norm_integrals_summable {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Summable (fun n => ∫ t : ℝ in Ioi 0, ‖complexGeneratingTailTerm χ u n t‖) :=
  (weighted_log_series_summable hu0 hu1).of_nonneg_of_le
    (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (complexGeneratingTailTerm_norm_integral_le χ hu0)

lemma complexGeneratingTailTerm_eq_summand {N : ℕ} (χ : DirichletCharacter ℂ N)
    (u : ℝ) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    complexGeneratingTailTerm χ u n t =
      generatingSummandHom χ (u : ℂ)
        (ne_zero_of_one_lt_re (show 1 < (1 + (t : ℂ)).re by simpa using ht)) (n + 2) := by
  have hn : n + 2 ≠ 0 := by omega
  unfold complexGeneratingTailTerm realGeneratingTailTerm
  simp only [generatingSummandHom, dirichletSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  rw [omegaWeightHom_apply hn]
  simp only [ofReal_mul, ofReal_pow, ofReal_cpow (by positivity : (0 : ℝ) ≤ n + 2),
    ofReal_neg, ofReal_add, ofReal_one, ofReal_natCast, ofReal_ofNat, Nat.cast_add, Nat.cast_ofNat]
  ring

/-- The exact termwise integral identity for every Dirichlet character, justified by absolute
summability of the integrals of norms. No coefficient-interchange hypothesis is assumed. -/
lemma integratedGeneratingValue_eq_weighted_series {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    integratedGeneratingValue χ u = ∑' n, weightedCharacterTerm χ u n := by
  have hu : ‖(u : ℂ)‖ ≤ 1 := by rw [Complex.norm_of_nonneg hu0]; exact hu1.le
  calc
    integratedGeneratingValue χ u = ∫ t : ℝ in Ioi 0, ∑' n, complexGeneratingTailTerm χ u n t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      have hs : 1 < (1 + (t : ℂ)).re := by simpa using ht
      rw [generatingValue_sub_one_eq_tail χ hu hs]
      apply tsum_congr
      intro n
      exact (complexGeneratingTailTerm_eq_summand χ u ht n).symm
    _ = ∑' n, ∫ t : ℝ in Ioi 0, complexGeneratingTailTerm χ u n t :=
      (integral_tsum_of_summable_integral_norm (complexGeneratingTailTerm_integrable χ u)
        (complexGeneratingTailTerm_norm_integrals_summable χ hu0 hu1)).symm
    _ = _ := tsum_congr (fun n => integral_complexGeneratingTailTerm χ u n)

lemma weightedCharacterTerm_summable {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) : Summable (weightedCharacterTerm χ u) := by
  have h := (hasSum_integral_of_summable_integral_norm (complexGeneratingTailTerm_integrable χ u)
    (complexGeneratingTailTerm_norm_integrals_summable χ hu0 hu1)).summable
  simpa only [integral_complexGeneratingTailTerm] using h

end Erdos143
