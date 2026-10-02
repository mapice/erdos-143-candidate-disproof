import Erdos143.WeightedIntegrability
import Erdos143.MomentKernel

noncomputable section
open MeasureTheory Set Complex

namespace Erdos143

lemma global_first_moment_integrable :
    IntegrableOn (fun t : ℝ => (t : ℂ) *
      (generatingValue (1 : DirichletCharacter ℂ 1) 1 (1 + (t : ℂ)) - 1)) (Ioi 0) := by
  have hu : ‖(1 : ℂ)‖ ≤ 1 := by simp
  have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) *
      (generatingValue (1 : DirichletCharacter ℂ 1) 1 (1 + (t : ℂ)) - 1)) (Ioi 0) :=
    continuous_ofReal.continuousOn.mul
      ((generatingValue_continuousOn_positive (1 : DirichletCharacter ℂ 1) hu).sub
        (continuousOn_const (c := (1 : ℂ))))
  obtain ⟨eps, heps0, heps1, hsmall⟩ := global_generating_local_upper
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply integrableOn_Ioi_of_power_exp_bounds hcont heps0 heps1
    (a := 0) (by norm_num) (show 0 < Real.log 2 / 2 by positivity)
    (C := 0) (D := 5) (E := tailMajorantConst * (2 / Real.log 2))
  · intro t ht hteps
    have hm := hsmall 1 (by norm_num) (by norm_num) t ht hteps
    simp only [Complex.ofReal_one, Real.rpow_neg_one] at hm
    have hm' := mul_le_mul_of_nonneg_left hm ht.le
    have hcancel : t * (4 * t⁻¹) = 4 := by field_simp
    rw [hcancel] at hm'
    have hn := norm_sub_le (generatingValue (1 : DirichletCharacter ℂ 1) 1 (1 + (t : ℂ))) (1 : ℂ)
    simp only [norm_one] at hn
    have hn' := mul_le_mul_of_nonneg_left hn ht.le
    rw [norm_mul, Complex.norm_of_nonneg ht.le]
    simp only [Real.rpow_zero, mul_one, zero_add]
    nlinarith [hteps.trans heps1]
  · intro t ht
    have ht0 : 0 ≤ t := by linarith
    rw [norm_mul, Complex.norm_of_nonneg ht0]
    have hb := mul_le_mul_of_nonneg_left (generatingValue_tail_bound (1 : DirichletCharacter ℂ 1) hu ht) ht0
    have he := mul_le_mul_of_nonneg_left (linear_exp_tail hc t) tailMajorantConst_nonneg
    nlinarith [hb, he]

def realMomentTerm (n : ℕ) (t : ℝ) : ℝ := max t 0 * realGeneratingTailTerm 1 n t

lemma realMomentTerm_nonneg (n : ℕ) (t : ℝ) : 0 ≤ realMomentTerm n t :=
  mul_nonneg (le_max_right _ _) (realGeneratingTailTerm_nonneg (by norm_num) n t)

lemma realMomentTerm_continuous (n : ℕ) : Continuous (realMomentTerm n) := by
  have hbase : ((n : ℝ) + 2) ≠ 0 := by positivity
  have hp : Continuous (fun t : ℝ => ((n : ℝ) + 2) ^ (-(1 + t))) :=
    (Real.continuous_const_rpow hbase).comp ((continuous_const (y := (1 : ℝ))).add continuous_id).neg
  have hm : Continuous (fun t : ℝ => max t 0) := continuous_id.max continuous_const
  unfold realMomentTerm realGeneratingTailTerm
  simpa only [one_pow, one_mul] using hm.mul hp

lemma realMomentTerm_summable {t : ℝ} (ht : 0 < t) : Summable (fun n => realMomentTerm n t) :=
  (realGeneratingTailTerm_summable (by norm_num : (0 : ℝ) ≤ 1) (by norm_num) ht).mul_left _

lemma realMoment_sum_eq_norm {t : ℝ} (ht : 0 < t) :
    (∑' n, realMomentTerm n t) = ‖(t : ℂ) *
      (generatingValue (1 : DirichletCharacter ℂ 1) 1 (1 + (t : ℂ)) - 1)‖ := by
  simp only [realMomentTerm, tsum_mul_left, max_eq_left ht.le, norm_mul, Complex.norm_of_nonneg ht.le]
  have h := global_sub_one_norm_eq_real_tail (u := 1) (by norm_num) (by norm_num) ht
  simpa only [Complex.ofReal_one] using congrArg (fun x : ℝ => t * x) h.symm

lemma realMoment_sum_integrable :
    IntegrableOn (fun t : ℝ => ∑' n, realMomentTerm n t) (Ioi 0) := by
  exact global_first_moment_integrable.norm.congr
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => (realMoment_sum_eq_norm ht).symm))

lemma realMomentTerm_integrable (n : ℕ) : IntegrableOn (realMomentTerm n) (Ioi 0) := by
  apply realMoment_sum_integrable.mono' (realMomentTerm_continuous n).aestronglyMeasurable
  apply ae_restrict_of_forall_mem measurableSet_Ioi
  intro t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (realMomentTerm_nonneg n t)]
  exact (realMomentTerm_summable ht).le_tsum n (fun i _ => realMomentTerm_nonneg i t)

lemma integral_realMomentTerm (n : ℕ) :
    (∫ t : ℝ in Ioi 0, realMomentTerm n t) =
      1 / (((n : ℝ) + 2) * (Real.log ((n : ℝ) + 2)) ^ 2) := by
  calc
    _ = ∫ t : ℝ in Ioi 0, t * ((n : ℝ) + 2) ^ (-(1 + t)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := ht
      simp only [realMomentTerm, realGeneratingTailTerm, max_eq_left ht0.le, one_pow, one_mul]
    _ = _ := real_log_moment_integral (by linarith [Nat.cast_nonneg (α := ℝ) n])

/-- The full logarithmic second moment converges; this controls every fixed gcd/log shift
in the passage to noninvertible residue classes. -/
lemma log_squared_weight_summable :
    Summable (fun n : ℕ => 1 / (((n : ℝ) + 2) * (Real.log ((n : ℝ) + 2)) ^ 2)) := by
  have h := summable_integral_of_integrable_tsum_nonneg realMomentTerm realMomentTerm_integrable
    realMomentTerm_nonneg
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => realMomentTerm_summable ht))
    realMoment_sum_integrable
  simpa only [integral_realMomentTerm] using h

end Erdos143
