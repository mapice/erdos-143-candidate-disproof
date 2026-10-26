import Erdos143.LogarithmicBounds
import Erdos143.PeriodicSelection

noncomputable section
open MeasureTheory Set Filter Complex DirichletCharacter
open scoped BigOperators Topology ArithmeticFunction.Omega ENNReal

namespace Erdos143.Logarithmic

attribute [local instance] Classical.propDecidable

/-- The sole analytic input of the logarithmic route; a closed instance is constructed below. -/
class Estimate : Prop where
  remainder : RemainderBound

variable [Estimate]

lemma global_generating_local_upper :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ t : ℝ, 0 < t → t ≤ eps →
      ‖generatingValue (1 : DirichletCharacter ℂ 1) (u : ℂ) (1 + (t : ℂ))‖ ≤
        (2 * Real.exp 1) * t ^ (-u) :=
  Bounds.global_generating_local_upper Estimate.remainder

lemma nonprincipal_generatingValue_bounded {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖generatingValue χ (u : ℂ) (1 + (t : ℂ))‖ ≤ C :=
  Bounds.nonprincipal_generatingValue_bounded Estimate.remainder χ hχ

lemma generatingValue_sub_one_integrable {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    IntegrableOn (fun t : ℝ => generatingValue χ (u : ℂ) (1 + (t : ℂ)) - 1) (Ioi 0) := by
  have hu : ‖(u : ℂ)‖ ≤ 1 := by rw [Complex.norm_of_nonneg hu0]; exact hu1.le
  have hcont := (generatingValue_continuousOn_positive χ hu).sub (continuousOn_const (c := (1 : ℂ)))
  obtain ⟨eps, heps0, heps1, hsmall⟩ := global_generating_local_upper
  apply integrableOn_Ioi_of_power_exp_bounds hcont heps0 heps1
    (show -1 < -u by linarith) (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    (C := 2 * Real.exp 1) (D := 1) (E := tailMajorantConst)
  · intro t ht hteps
    have hdom := generatingValue_norm_le_global χ hu0 hu1.le (show (1 : ℝ) < 1 + t by linarith)
    simp only [Complex.ofReal_add, Complex.ofReal_one] at hdom
    have hmajor := hsmall u hu0 hu1.le t ht hteps
    calc
      _ ≤ ‖generatingValue χ (u : ℂ) (1 + (t : ℂ))‖ + 1 := by
        simpa only [norm_one] using norm_sub_le (generatingValue χ (u : ℂ) (1 + (t : ℂ))) (1 : ℂ)
      _ ≤ _ := by linarith
  · intro t ht
    exact generatingValue_tail_bound χ hu ht

/-- Integrability of the nonnegative series follows from the new logarithmic majorant. -/

lemma realGeneratingTail_sum_integrable {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    IntegrableOn (fun t : ℝ => ∑' n, realGeneratingTailTerm u n t) (Ioi 0) := by
  have h := (generatingValue_sub_one_integrable (1 : DirichletCharacter ℂ 1) hu0 hu1).norm
  exact h.congr (ae_restrict_of_forall_mem measurableSet_Ioi
    (fun t ht => global_sub_one_norm_eq_real_tail hu0 hu1.le ht))

/-- Absolute convergence of the Ω-weighted logarithmic series is proved, rather than assumed. -/

lemma weighted_log_series_summable {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Summable (fun n : ℕ => u ^ Ω (n + 2) / (((n : ℝ) + 2) * Real.log ((n : ℝ) + 2))) := by
  have h := summable_integral_of_integrable_tsum_nonneg (realGeneratingTailTerm u)
    (realGeneratingTailTerm_integrable u) (realGeneratingTailTerm_nonneg hu0)
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => realGeneratingTailTerm_summable hu0 hu1.le ht))
    (realGeneratingTail_sum_integrable hu0 hu1)
  simpa only [integral_realGeneratingTailTerm] using h

lemma complexGeneratingTailTerm_norm_integrals_summable {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Summable (fun n => ∫ t : ℝ in Ioi 0, ‖complexGeneratingTailTerm χ u n t‖) :=
  (weighted_log_series_summable hu0 hu1).of_nonneg_of_le
    (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (complexGeneratingTailTerm_norm_integral_le χ hu0)

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

lemma realAbelTerm_summable {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) : Summable (realAbelTerm u) := by
  apply (summable_nat_add_iff 2).mp
  simpa only [realAbelTerm, natWeight, Nat.cast_add, Nat.cast_ofNat, mul_one_div] using
    weighted_log_series_summable hu0 hu1

lemma fullWeightedCharacterTerm_summable {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) : Summable (fullWeightedCharacterTerm χ u) := by
  apply (summable_nat_add_iff 2).mp
  simpa only [fullWeightedCharacterTerm_shift] using weightedCharacterTerm_summable χ hu0 hu1

lemma integratedGeneratingValue_eq_full_series {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    integratedGeneratingValue χ u = ∑' n, fullWeightedCharacterTerm χ u n := by
  rw [integratedGeneratingValue_eq_weighted_series χ hu0 hu1]
  have h := (fullWeightedCharacterTerm_summable χ hu0 hu1).sum_add_tsum_nat_add 2
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, fullWeightedCharacterTerm_zero,
    fullWeightedCharacterTerm_one, zero_add, fullWeightedCharacterTerm_shift] using h

lemma progressionTerm_summable {N : ℕ} (b : ZMod N) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Summable (progressionTerm N b u) := by
  apply (realAbelTerm_summable hu0 hu1).of_nonneg_of_le (progressionTerm_nonneg b hu0)
  intro n
  unfold progressionTerm
  split_ifs
  · exact le_rfl
  · exact realAbelTerm_nonneg hu0 n

lemma progressionMass_orthogonality {N : ℕ} [NeZero N] {b : ZMod N} (hb : IsUnit b)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (progressionMass N b u : ℂ) = (N.totient : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ N, χ b⁻¹ * integratedGeneratingValue χ u := by
  unfold progressionMass
  rw [Complex.ofReal_tsum]
  simp_rw [progressionTerm_orthogonality hb]
  rw [tsum_mul_left]
  congr 1
  rw [Summable.tsum_finsetSum (fun χ _ => (fullWeightedCharacterTerm_summable χ hu0 hu1).mul_left _)]
  apply Finset.sum_congr rfl
  intro χ _
  rw [tsum_mul_left, integratedGeneratingValue_eq_full_series χ hu0 hu1]

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
    (C := 0) (D := 2 * Real.exp 1 + 1) (E := tailMajorantConst * (2 / Real.log 2))
  · intro t ht hteps
    have hm := hsmall 1 (by norm_num) (by norm_num) t ht hteps
    simp only [Complex.ofReal_one, Real.rpow_neg_one] at hm
    have hm' := mul_le_mul_of_nonneg_left hm ht.le
    have hcancel : t * ((2 * Real.exp 1) * t⁻¹) = 2 * Real.exp 1 := by field_simp
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

lemma log_squared_weight_summable :
    Summable (fun n : ℕ => 1 / (((n : ℝ) + 2) * (Real.log ((n : ℝ) + 2)) ^ 2)) := by
  have h := summable_integral_of_integrable_tsum_nonneg realMomentTerm realMomentTerm_integrable
    realMomentTerm_nonneg
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => realMomentTerm_summable ht))
    realMoment_sum_integrable
  simpa only [integral_realMomentTerm] using h

lemma momentWeight_summable : Summable momentWeight := by
  apply (summable_nat_add_iff 2).mp
  simpa only [momentWeight, Nat.cast_add, Nat.cast_ofNat] using log_squared_weight_summable

/-- Nonprincipal integrals are uniformly bounded, including the endpoint u=1. -/

lemma nonprincipal_integratedGeneratingValue_bounded {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ‖integratedGeneratingValue χ u‖ ≤ K := by
  obtain ⟨C, hC0, hC⟩ := nonprincipal_generatingValue_bounded χ hχ
  let g : ℝ → ℝ := fun t => (Ioc (0 : ℝ) 1).indicator (fun _ => C + 1) t +
    tailMajorantConst * Real.exp ((-Real.log 2) * t)
  have hind : IntegrableOn (fun t => (Ioc (0 : ℝ) 1).indicator (fun _ => C + 1) t) (Ioi 0) := by
    have hc : IntegrableOn (fun _ : ℝ => C + 1) (Ioc 0 1) :=
      (continuous_const.integrableOn_Icc (a := (0 : ℝ)) (b := 1)).mono_set Ioc_subset_Icc_self
    exact (hc.integrable_indicator measurableSet_Ioc).integrableOn
  have hexp : IntegrableOn (fun t => tailMajorantConst * Real.exp ((-Real.log 2) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]) 0).const_mul _
  have hg : IntegrableOn g (Ioi 0) := hind.add hexp
  have hg0 (t : ℝ) : 0 ≤ g t := by
    unfold g
    apply add_nonneg
    · by_cases ht : t ∈ Ioc (0 : ℝ) 1
      · rw [indicator_of_mem ht]
        linarith
      · rw [indicator_of_notMem ht]
    · exact mul_nonneg tailMajorantConst_nonneg (Real.exp_pos _).le
  refine ⟨∫ t : ℝ in Ioi 0, g t, integral_nonneg hg0, ?_⟩
  intro u hu0 hu1
  have hu : ‖(u : ℂ)‖ ≤ 1 := by rw [Complex.norm_of_nonneg hu0]; exact hu1
  apply norm_integral_le_of_norm_le hg
  apply ae_restrict_of_forall_mem measurableSet_Ioi
  intro t ht
  change ‖generatingValue χ (u : ℂ) (1 + (t : ℂ)) - 1‖ ≤ g t
  unfold g
  by_cases ht1 : t ≤ 1
  · rw [indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht, ht1⟩)]
    have hb := hC u hu0 hu1 t ht ht1
    have hn := norm_sub_le (generatingValue χ (u : ℂ) (1 + (t : ℂ))) (1 : ℂ)
    simp only [norm_one] at hn
    have he := mul_nonneg tailMajorantConst_nonneg (Real.exp_pos ((-Real.log 2) * t)).le
    linarith
  · rw [indicator_of_notMem (show t ∉ Ioc (0 : ℝ) 1 by intro h; exact ht1 h.2), zero_add]
    exact generatingValue_tail_bound χ hu (le_of_not_ge ht1)

/-- The nonprincipal contribution vanishes after Abel normalization. -/

lemma nonprincipal_normalized_integral_tendsto_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    Tendsto (fun u : ℝ => (1 - (u : ℂ)) * integratedGeneratingValue χ u) (𝓝[<] 1) (𝓝 0) := by
  obtain ⟨K, _hK0, hK⟩ := nonprincipal_integratedGeneratingValue_bounded χ hχ
  have hbound : ∀ᶠ u : ℝ in 𝓝[<] 1,
      ‖(1 - (u : ℂ)) * integratedGeneratingValue χ u‖ ≤ (1 - u) * K := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with u hu
    have hu0 : 0 ≤ u := hu.1.le
    have hu1 : u ≤ 1 := hu.2.le
    have hnorm : ‖1 - (u : ℂ)‖ = 1 - u := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_of_nonneg (by linarith)]
    rw [norm_mul, hnorm]
    exact mul_le_mul_of_nonneg_left (hK u hu0 hu1) (by linarith)
  have hid : Tendsto (fun u : ℝ => u) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
  have hlim : Tendsto (fun u : ℝ => (1 - u) * K) (𝓝[<] 1) (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hid).mul_const K
  exact squeeze_zero_norm' hbound hlim

lemma principalRealIntegrand_integrable {N : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    IntegrableOn (principalRealIntegrand N u) (Ioi 0) := by
  have h := (generatingValue_sub_one_integrable (1 : DirichletCharacter ℂ N) hu0 hu1).re
  apply h.congr
  exact ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => principalRealIntegrand_eq_re hu0 ht)

lemma principal_integrated_re_eq_real_integral {N : ℕ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (integratedGeneratingValue (1 : DirichletCharacter ℂ N) u).re =
      ∫ t : ℝ in Ioi 0, principalRealIntegrand N u t := by
  have h := generatingValue_sub_one_integrable (1 : DirichletCharacter ℂ N) hu0 hu1
  calc
    _ = ∫ t : ℝ in Ioi 0, (generatingValue (1 : DirichletCharacter ℂ N) (u : ℂ) (1 + (t : ℂ)) - 1).re := by
      exact (Complex.reCLM.integral_comp_comm h).symm
    _ = _ := setIntegral_congr_fun measurableSet_Ioi (fun t ht => principalRealIntegrand_eq_re hu0 ht)

omit [Estimate] in
lemma integral_abel_power_kernel {u eps k : ℝ} (hu : u < 1) (heps : 0 < eps) :
    (∫ t : ℝ in Ioo 0 eps, (1 / 2 : ℝ) * (k / 2) ^ u * t ^ (-u) - 1) =
      (1 / 2 : ℝ) * (k / 2) ^ u * eps ^ (1 - u) / (1 - u) - eps := by
  have hp : IntegrableOn (fun t : ℝ => t ^ (-u)) (Ioo 0 eps) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff heps).2 (by linarith)
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 eps) :=
    (continuous_const.integrableOn_Icc (a := (0 : ℝ)) (b := eps)).mono_set Ioo_subset_Icc_self
  rw [integral_sub (hp.const_mul _) hc, integral_const_mul, Erdos143.integral_Ioo_neg_rpow hu heps,
    setIntegral_const, Real.volume_real_Ioo, sub_zero, max_eq_left heps.le]
  simp only [smul_eq_mul, mul_one]
  ring

lemma principal_integrated_re_lower {N : ℕ} [NeZero N] :
    ∃ eps : ℝ, 0 < eps ∧ ∀ u : ℝ, 1 / 2 ≤ u → u < 1 →
      (1 / 2 : ℝ) * (totientRatio N / 2) ^ u * eps ^ (1 - u) / (1 - u) - eps ≤
        (integratedGeneratingValue (1 : DirichletCharacter ℂ N) u).re := by
  obtain ⟨eps, heps0, _heps1, hpoint⟩ := Bounds.principal_generating_local_lower Estimate.remainder N
  refine ⟨eps, heps0, ?_⟩
  intro u hu0 hu1
  have hu0' : 0 ≤ u := by linarith
  have hF := principalRealIntegrand_integrable (N := N) hu0' hu1
  have hFI : IntegrableOn (principalRealIntegrand N u) (Ioo 0 eps) := hF.mono_set Ioo_subset_Ioi_self
  have hp : IntegrableOn (fun t : ℝ => t ^ (-u)) (Ioo 0 eps) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff heps0).2 (by linarith)
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 eps) :=
    (continuous_const.integrableOn_Icc (a := (0 : ℝ)) (b := eps)).mono_set Ioo_subset_Icc_self
  rw [principal_integrated_re_eq_real_integral hu0' hu1, ← integral_abel_power_kernel hu1 heps0]
  calc
    _ ≤ ∫ t : ℝ in Ioo 0 eps, principalRealIntegrand N u t := by
      apply integral_mono_ae ((hp.const_mul _).sub hc) hFI
      apply ae_restrict_of_forall_mem measurableSet_Ioo
      intro t ht
      have h := hpoint u hu0 hu1.le t ht.1 ht.2.le
      have hratio : totientRatio N / (2 * t) = (totientRatio N / 2) / t := by ring
      have hk0 : (0 : ℝ) ≤ totientRatio N / 2 := div_nonneg (totientRatio_pos N).le (by norm_num)
      rw [hratio, Real.div_rpow hk0 ht.1.le] at h
      simp only [div_eq_mul_inv, ← Real.rpow_neg ht.1.le] at h
      change (1 / 2 : ℝ) * (totientRatio N / 2) ^ u * t ^ (-u) - 1 ≤
        ‖generatingValue (1 : DirichletCharacter ℂ N) (u : ℂ) (1 + (t : ℂ))‖ - 1
      have h' : (1 / 2 : ℝ) * (totientRatio N / 2) ^ u * t ^ (-u) ≤
          ‖generatingValue (1 : DirichletCharacter ℂ N) (u : ℂ) (1 + (t : ℂ))‖ := by
        simpa only [div_eq_mul_inv, mul_assoc] using h
      exact sub_le_sub_right h' 1
    _ ≤ _ := setIntegral_mono_set hF
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => principalRealIntegrand_nonneg hu0' hu1.le ht))
      (Eventually.of_forall (fun _ ht => ht.1))

lemma principal_abel_lower_bound (N : ℕ) [NeZero N] :
    HasAbelLowerBound (fun u : ℝ => (1 - u) *
      (integratedGeneratingValue (1 : DirichletCharacter ℂ N) u).re) (totientRatio N / 4) := by
  obtain ⟨eps, heps, hlower⟩ := principal_integrated_re_lower (N := N)
  let g : ℝ → ℝ := fun u => (1 / 2 : ℝ) * (totientRatio N / 2) ^ u * eps ^ (1 - u) - (1 - u) * eps
  have hid : Tendsto (fun u : ℝ => u) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
  have hk : totientRatio N / 2 ≠ 0 := ne_of_gt (div_pos (totientRatio_pos N) (by norm_num))
  have hg : Tendsto g (𝓝[<] 1) (𝓝 (totientRatio N / 4)) := by
    have ha := (tendsto_const_nhds (x := totientRatio N / 2)).rpow hid (Or.inl hk)
    have hb := (tendsto_const_nhds (x := eps)).rpow
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hid) (Or.inl heps.ne')
    have hc := ((tendsto_const_nhds (x := (1 : ℝ))).sub hid).mul_const eps
    convert ((ha.const_mul (1 / 2 : ℝ)).mul hb).sub hc using 1
    simp only [sub_self, Real.rpow_zero, Real.rpow_one, mul_one, zero_mul, sub_zero]
    ring
  apply hasAbelLowerBound_of_tendsto_minorant hg
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with u hu
  have h := mul_le_mul_of_nonneg_left (hlower u hu.1.le hu.2) (sub_nonneg.mpr hu.2.le)
  have hne : 1 - u ≠ 0 := by linarith [hu.2]
  dsimp [g]
  convert h using 1
  field_simp

lemma characterError_tendsto_zero {N : ℕ} [NeZero N] (b : ZMod N) :
    Tendsto (characterError b) (𝓝[<] 1) (𝓝 0) := by
  classical
  have h := tendsto_finset_sum ((Finset.univ : Finset (DirichletCharacter ℂ N)).erase 1)
    (fun χ hχ => (nonprincipal_normalized_integral_tendsto_zero χ (Finset.mem_erase.mp hχ).1).const_mul (χ b⁻¹))
  simpa only [characterError, mul_zero, Finset.sum_const_zero] using h

lemma normalized_progression_identity {N : ℕ} [NeZero N] {b : ZMod N} (hb : IsUnit b)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (1 - u) * progressionMass N b u = (N.totient : ℝ)⁻¹ *
      ((1 - u) * (integratedGeneratingValue (1 : DirichletCharacter ℂ N) u).re + (characterError b u).re) := by
  classical
  have horth := progressionMass_orthogonality hb hu0 hu1
  have hcomplex : (1 - (u : ℂ)) * (progressionMass N b u : ℂ) = (N.totient : ℂ)⁻¹ *
      ((1 - (u : ℂ)) * integratedGeneratingValue (1 : DirichletCharacter ℂ N) u + characterError b u) := by
    calc
      _ = (N.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ N,
          χ b⁻¹ * ((1 - (u : ℂ)) * integratedGeneratingValue χ u) := by
        rw [horth, mul_left_comm (1 - (u : ℂ)) (N.totient : ℂ)⁻¹, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro χ _
        ring
      _ = _ := by
        congr 1
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ N))]
        simp only [principal_character_inverse_unit hb, one_mul]
        exact add_comm _ _
  have hphi : (N.totient : ℂ)⁻¹ = (((N.totient : ℝ)⁻¹ : ℝ) : ℂ) := by simp
  have huco : 1 - (u : ℂ) = ((1 - u : ℝ) : ℂ) := by push_cast; rfl
  rw [hphi, huco] at hcomplex
  have hreal := congrArg Complex.re hcomplex
  simpa only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero] using hreal

/-- The required positive Abel lower bound in every invertible residue class. -/

lemma coprime_progression_abel_lower_bound {N : ℕ} [NeZero N] {b : ZMod N} (hb : IsUnit b) :
    HasAbelLowerBound (fun u : ℝ => (1 - u) * progressionMass N b u) (1 / (4 * (N : ℝ))) := by
  have hE : Tendsto (fun u => (characterError b u).re) (𝓝[<] 1) (𝓝 0) := by
    simpa using (continuous_re.tendsto 0).comp (characterError_tendsto_zero b)
  have hφ : (0 : ℝ) < N.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos N)
  have hscaled := ((principal_abel_lower_bound N).add_vanishing hE).mul_pos (inv_pos.mpr hφ)
  have heq : (N.totient : ℝ)⁻¹ * (totientRatio N / 4) = 1 / (4 * (N : ℝ)) := by
    have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
    unfold totientRatio
    field_simp
  rw [heq] at hscaled
  apply hscaled.mono
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with u hu
  exact (normalized_progression_identity hb hu.1.le hu.2).symm.le

lemma progressionMass_scale_lower {g M c : ℕ} (hg : 1 ≤ g)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (u ^ Ω g / (g : ℝ)) * progressionMass M (c : ZMod M) u - shiftPenalty g ≤
      progressionMass (g * M) ((g * c : ℕ) : ZMod (g * M)) u := by
  have hinj : Function.Injective (fun n : ℕ => g * n) := by
    intro n m h
    exact mul_left_cancel₀ (by omega : g ≠ 0) h
  have hM := progressionTerm_summable (c : ZMod M) hu0 hu1
  have hT := progressionTerm_summable (((g * c : ℕ) : ZMod (g * M))) hu0 hu1
  have hmap := hT.comp_injective hinj
  have hsrc := (hM.mul_left (u ^ Ω g / (g : ℝ))).sub
    (momentWeight_summable.mul_left (Real.log g / (g : ℝ)))
  have hle := hsrc.tsum_le_tsum (fun n => progressionTerm_scale_lower (M := M) (c := c) (n := n) hg hu0 hu1.le) hmap
  rw [Summable.tsum_sub (hM.mul_left _) (momentWeight_summable.mul_left _), tsum_mul_left, tsum_mul_left] at hle
  have hsubset := hmap.tsum_le_tsum_of_inj (fun n : ℕ => g * n) hinj
    (fun n _ => progressionTerm_nonneg _ hu0 n) (fun _ => le_rfl) hT
  exact hle.trans hsubset

lemma scaled_progression_abel_lower_bound {g M c : ℕ} [NeZero M] (hg : 1 ≤ g)
    (hc : IsUnit (c : ZMod M)) :
    HasAbelLowerBound
      (fun u : ℝ => (1 - u) * progressionMass (g * M) ((g * c : ℕ) : ZMod (g * M)) u)
      (1 / (4 * ((g * M : ℕ) : ℝ))) := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hMR : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hbase := coprime_progression_abel_lower_bound hc
  have hid : Tendsto (fun u : ℝ => u) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
  have hcoef : Tendsto (fun u : ℝ => u ^ Ω g / (g : ℝ)) (𝓝[<] 1) (𝓝 (1 / (g : ℝ))) := by
    simpa only [one_pow] using (hid.pow (Ω g)).div_const (g : ℝ)
  have hmul := hbase.mul_tendsto_pos (by positivity : (0 : ℝ) < 1 / (4 * (M : ℝ)))
    hcoef (by positivity : (0 : ℝ) < 1 / (g : ℝ))
  have herr : Tendsto (fun u : ℝ => -(1 - u) * shiftPenalty g) (𝓝[<] 1) (𝓝 0) := by
    simpa using (((tendsto_const_nhds (x := (1 : ℝ))).sub hid).neg).mul_const (shiftPenalty g)
  have hbound := hmul.add_vanishing herr
  have hconst : (1 / (g : ℝ)) * (1 / (4 * (M : ℝ))) = 1 / (4 * ((g * M : ℕ) : ℝ)) := by
    push_cast
    field_simp
  rw [hconst] at hbound
  apply hbound.mono
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with u hu
  have h := mul_le_mul_of_nonneg_left (progressionMass_scale_lower (M := M) (c := c) hg hu.1.le hu.2)
    (show 0 ≤ 1 - u by linarith [hu.2])
  convert h using 1
  ring

/-- The positive Abel lower bound includes every residue, with no coprimality omission. -/

lemma all_residues_abel_lower_bound (N : ℕ) [NeZero N] (b : ZMod N) :
    HasAbelLowerBound (fun u : ℝ => (1 - u) * progressionMass N b u) (1 / (4 * (N : ℝ))) := by
  let n : ℕ := b.val
  let g : ℕ := Nat.gcd n N
  let M : ℕ := N / g
  let c : ℕ := n / g
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right n (NeZero.pos N)
  have hM0 : 0 < M := Nat.div_pos (Nat.gcd_le_right n (NeZero.pos N)) hg0
  letI : NeZero M := ⟨hM0.ne'⟩
  have hcop : Nat.Coprime c M := Nat.coprime_div_gcd_div_gcd hg0
  have hc : IsUnit (c : ZMod M) := (ZMod.isUnit_iff_coprime c M).2 hcop
  have h := scaled_progression_abel_lower_bound (g := g) (M := M) (c := c) (by omega) hc
  have hN : g * M = N := Nat.mul_div_cancel' (Nat.gcd_dvd_right n N)
  have hn : g * c = n := Nat.mul_div_cancel' (Nat.gcd_dvd_left n N)
  have hfun : (fun u : ℝ => (1 - u) * progressionMass (g * M) ((g * c : ℕ) : ZMod (g * M)) u) =
      fun u : ℝ => (1 - u) * progressionMass N b u := by
    funext u
    congr 1
    calc
      _ = progressionMass N (n : ZMod N) u := progressionMass_natCast_congr hN hn u
      _ = _ := by rw [show (n : ZMod N) = b from ZMod.natCast_zmod_val b]
  rw [hfun] at h
  simpa only [hN] using h

lemma setAbelMass_periodic (L : ℕ) (S : Finset (ZMod L)) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    setAbelMass (periodicResidueSet L S) u = ∑ b ∈ S, progressionMass L b u := by
  classical
  have hterm (n : ℕ) : (periodicResidueSet L S).indicator (realAbelTerm u) n =
      ∑ b ∈ S, progressionTerm L b u n := by
    simp [periodicResidueSet, progressionTerm, Set.indicator_apply]
  unfold setAbelMass
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun b _ => progressionTerm_summable b hu0 hu1)]
  rfl

/-- A fixed periodic set has an Abel lower bound proportional to all its residue classes. -/

lemma periodic_abel_lower_bound (L : ℕ) [NeZero L] (S : Finset (ZMod L)) :
    HasAbelLowerBound (fun u : ℝ => (1 - u) * setAbelMass (periodicResidueSet L S) u)
      ((S.card : ℝ) / (4 * (L : ℝ))) := by
  have h := HasAbelLowerBound.sum S (fun b _ => all_residues_abel_lower_bound L b)
  have hconstant : (∑ _b ∈ S, (1 / (4 * (L : ℝ)))) = (S.card : ℝ) / (4 * (L : ℝ)) := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  rw [hconstant] at h
  apply h.mono
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with u hu
  rw [setAbelMass_periodic L S hu.1.le hu.2, Finset.mul_sum]

lemma layer_weight_summable (E : Set ℕ) (r : ℕ) :
    Summable (fun n : ℕ => if Ω n = r ∧ n ∈ E then natWeight n else 0) := by
  classical
  have hsum := (realAbelTerm_summable (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_left ((2 : ℝ) ^ r)
  apply hsum.of_nonneg_of_le
  · intro n
    split_ifs
    · exact natWeight_nonneg n
    · exact le_rfl
  · intro n
    by_cases hn : Ω n = r ∧ n ∈ E
    · rw [if_pos hn]
      unfold realAbelTerm
      rw [hn.1]
      have hcancel : (2 : ℝ) ^ r * (1 / 2) ^ r = 1 := by rw [← mul_pow]; norm_num
      rw [← mul_assoc, hcancel, one_mul]
    · rw [if_neg hn]
      exact mul_nonneg (by positivity) (realAbelTerm_nonneg (by norm_num) n)

lemma setAbelTerm_summable (E : Set ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Summable (E.indicator (realAbelTerm u)) := (realAbelTerm_summable hu0 hu1).indicator E

/-- Grouping by Ω is justified by absolute summability, and counts multiplicity exactly. -/

lemma layer_abel_hasSum (E : Set ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    HasSum (fun r : ℕ => u ^ r * layerMass E r) (setAbelMass E u) := by
  classical
  have hsum := (setAbelTerm_summable E hu0 hu1).hasSum.tsum_fiberwise Ω
  have hfiber (r : ℕ) :
      (∑' n : {n : ℕ | Ω n = r}, E.indicator (realAbelTerm u) n) = u ^ r * layerMass E r := by
    calc
      _ = ∑' n : {n : ℕ | Ω n = r}, u ^ r * E.indicator natWeight n := by
        apply tsum_congr
        intro n
        have hn : Ω (n : ℕ) = r := n.property
        by_cases hE : (n : ℕ) ∈ E
        · simp only [Set.indicator_of_mem hE, realAbelTerm, hn]
        · simp only [Set.indicator_of_notMem hE, mul_zero]
      _ = _ := tsum_mul_left
  change HasSum (fun r => ∑' n : {n : ℕ | Ω n = r}, E.indicator (realAbelTerm u) n)
    (setAbelMass E u) at hsum
  simpa only [hfiber] using hsum

lemma exists_large_layer_of_abel_lower (E : Set ℕ) {c d : ℝ} (hc : 0 ≤ c) (hcd : c < d)
    (hAbel : HasAbelLowerBound (fun u : ℝ => (1 - u) * setAbelMass E u) d) (R : ℕ) :
    ∃ r : ℕ, R ≤ r ∧ c < layerMass E r := by
  by_contra hnot
  have htail : ∀ r, R ≤ r → layerMass E r ≤ c := by
    intro r hr
    by_contra hgt
    exact hnot ⟨r, hr, lt_of_not_ge hgt⟩
  let K : ℝ := ∑ r ∈ Finset.range R, layerMass E r
  have hupper : ∀ᶠ u : ℝ in 𝓝[<] 1, (1 - u) * setAbelMass E u ≤ c + (1 - u) * K := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with u hu
    have hs := layer_abel_hasSum E hu.1.le hu.2
    have h := normalized_power_series_upper_of_tail (layerMass_nonneg E) hc R htail hu.1.le hu.2 hs.summable
    rwa [hs.tsum_eq] at h
  have hid : Tendsto (fun u : ℝ => u) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
  have hlim : Tendsto (fun u : ℝ => c + (1 - u) * K) (𝓝[<] 1) (𝓝 c) := by
    simpa using (tendsto_const_nhds (x := c)).add (((tendsto_const_nhds (x := (1 : ℝ))).sub hid).mul_const K)
  have hm1 : c < (c + d) / 2 := by linarith
  have hm2 : (c + d) / 2 < d := by linarith
  obtain ⟨u, hu, hl, hh⟩ := (hupper.and ((hAbel ((c + d) / 2) hm2).and
    (hlim.eventually (eventually_lt_nhds hm1)))).exists
  linarith

lemma finite_primitive_from_layer (E : Set ℕ) {r N : ℕ} (hr : 0 < r) (hNr : N ≤ r)
    {c : ℝ} (hc : c < layerMass E r) :
    ∃ P : Finset ℕ, (∀ n ∈ P, N ≤ n ∧ n ∈ E) ∧ Primitive (P : Set ℕ) ∧
      c < ∑ n ∈ P, natWeight n := by
  classical
  let f : ℕ → ℝ := fun n => if Ω n = r ∧ n ∈ E then natWeight n else 0
  have hsum : HasSum f (layerMass E r) := by
    rw [layerMass_eq_tsum_conditional]
    exact (layer_weight_summable E r).hasSum
  change Tendsto (fun T : Finset ℕ => ∑ n ∈ T, f n) atTop (𝓝 (layerMass E r)) at hsum
  obtain ⟨T, hT⟩ := (hsum.eventually (eventually_gt_nhds hc)).exists
  let P := T.filter (fun n => Ω n = r ∧ n ∈ E)
  have hP : ∀ n ∈ P, Ω n = r ∧ n ∈ E := fun n hn => (Finset.mem_filter.mp hn).2
  refine ⟨P, ?_, ?_, ?_⟩
  · intro n hn
    refine ⟨?_, (hP n hn).2⟩
    calc
      N ≤ r := hNr
      _ = Ω n := (hP n hn).1.symm
      _ ≤ n := omega_le_self n
  · exact primitive_of_constant_omega hr (fun n hn => (hP n hn).1)
  · simpa only [P, Finset.sum_filter, f] using hT

lemma periodic_primitive_selection_real (L : ℕ) [NeZero L] (S : Finset (ZMod L))
    (hd : (2 / 3 : ℝ) < (S.card : ℝ) / L) (N : ℕ) (hN : 2 ≤ N) :
    ∃ P : Finset ℕ, (∀ n ∈ P, N ≤ n ∧ (n : ZMod L) ∈ S) ∧ Primitive (P : Set ℕ) ∧
      (1 / 6 : ℝ) < ∑ n ∈ P, natWeight n := by
  have hL : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
  have hc : (1 / 6 : ℝ) < (S.card : ℝ) / (4 * (L : ℝ)) := by
    have hd' := (lt_div_iff₀ hL).mp hd
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * L)).2
    nlinarith
  obtain ⟨r, hrN, hr⟩ := exists_large_layer_of_abel_lower (periodicResidueSet L S)
    (by norm_num : (0 : ℝ) ≤ 1 / 6) hc (periodic_abel_lower_bound L S) N
  obtain ⟨P, hP, hprim, hweight⟩ := finite_primitive_from_layer (periodicResidueSet L S)
    (by omega : 0 < r) hrN hr
  exact ⟨P, hP, hprim, hweight⟩

lemma periodic_primitive_selection (L : ℕ) [NeZero L] (S : Finset (ZMod L))
    (hd : (2 / 3 : ℝ) < (S.card : ℝ) / L) (N : ℕ) (hN : 2 ≤ N) :
    ∃ P : Finset ℕ, (∀ n ∈ P, N ≤ n ∧ (n : ZMod L) ∈ S) ∧ Primitive (P : Set ℕ) ∧
      (1 / 6 : ℝ≥0∞) < ∑ n ∈ P, weight n := by
  obtain ⟨P, hP, hprim, hw⟩ := periodic_primitive_selection_real L S hd N hN
  refine ⟨P, hP, hprim, ?_⟩
  have h := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6)).2 hw
  rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => natWeight_nonneg n)] at h
  simpa only [weight_nat_eq_ofReal, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 6),
    ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using h

/-- This closes exactly the finite-period interface stated at the start of the project,
including its original `Fin L` residue encoding and rational density comparison. -/

theorem periodicPrimitiveSelection_proved : PeriodicPrimitiveSelection := by
  intro L hL S hd N hN
  cases L with
  | zero => omega
  | succ L =>
    have hdR : (2 / 3 : ℝ) < (S.card : ℝ) / (L + 1 : ℕ) := by
      have hcast : (((2 / 3 : ℚ) : ℝ)) < (((S.card : ℚ) / (L + 1 : ℕ) : ℚ) : ℝ) :=
        Rat.cast_lt.mpr hd
      push_cast at hcast
      simpa only [Nat.cast_add, Nat.cast_one] using hcast
    obtain ⟨P, hP, hprim, hw⟩ := periodic_primitive_selection (L + 1) S hdR N hN
    refine ⟨P, ?_, hprim, hw⟩
    intro n hn
    refine ⟨(hP n hn).1, ?_⟩
    have heq : (n : ZMod (L + 1)) =
        (⟨n % (L + 1), Nat.mod_lt n hL⟩ : Fin (L + 1)) := by
      apply Fin.ext
      exact ZMod.val_natCast (L + 1) n
    rw [← heq]
    exact (hP n hn).2

end Erdos143.Logarithmic
