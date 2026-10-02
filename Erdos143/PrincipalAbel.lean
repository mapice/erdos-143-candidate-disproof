import Erdos143.TwistedIntegral
import Erdos143.PrincipalResidue
import Erdos143.AbelBounds

noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology

namespace Erdos143

def principalRealIntegrand (N : ℕ) (u t : ℝ) : ℝ :=
  ‖generatingValue (1 : DirichletCharacter ℂ N) (u : ℂ) (1 + (t : ℂ))‖ - 1

lemma principalRealIntegrand_eq_re {N : ℕ} {u t : ℝ} (hu : 0 ≤ u) (ht : 0 < t) :
    (generatingValue (1 : DirichletCharacter ℂ N) (u : ℂ) (1 + (t : ℂ)) - 1).re =
      principalRealIntegrand N u t := by
  have hs : (1 : ℝ) < 1 + t := by linarith
  have heq := principalGeneratingValue_eq_real_sum (N := N) (u := u) hs
  simp only [ofReal_add, ofReal_one] at heq
  unfold principalRealIntegrand
  rw [heq, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
    Complex.norm_of_nonneg (tsum_nonneg (principalGeneratingTerm_nonneg hu))]

lemma principalRealIntegrand_nonneg {N : ℕ} {u t : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ht : 0 < t) : 0 ≤ principalRealIntegrand N u t := by
  have h := principalGeneratingValue_norm_one_le (N := N) hu0 hu1 (show (1 : ℝ) < 1 + t by linarith)
  simp only [ofReal_add, ofReal_one] at h
  exact sub_nonneg.mpr h

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

lemma integral_Ioo_neg_rpow {u eps : ℝ} (hu : u < 1) (heps : 0 < eps) :
    (∫ t : ℝ in Ioo 0 eps, t ^ (-u)) = eps ^ (1 - u) / (1 - u) := by
  have h := integral_rpow (a := 0) (b := eps) (r := -u) (Or.inl (by linarith : -1 < -u))
  rw [intervalIntegral.integral_of_le heps.le, integral_Ioc_eq_integral_Ioo] at h
  have he : -u + 1 = 1 - u := by ring
  simpa only [he, Real.zero_rpow (by linarith : 1 - u ≠ 0), sub_zero] using h

lemma integral_abel_power_kernel {u eps k : ℝ} (hu : u < 1) (heps : 0 < eps) :
    (∫ t : ℝ in Ioo 0 eps, (k / 4) ^ u * t ^ (-u) - 1) =
      (k / 4) ^ u * eps ^ (1 - u) / (1 - u) - eps := by
  have hp : IntegrableOn (fun t : ℝ => t ^ (-u)) (Ioo 0 eps) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff heps).2 (by linarith)
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 eps) :=
    (continuous_const.integrableOn_Icc (a := (0 : ℝ)) (b := eps)).mono_set Ioo_subset_Icc_self
  rw [integral_sub (hp.const_mul _) hc, integral_const_mul, integral_Ioo_neg_rpow hu heps,
    setIntegral_const, Real.volume_real_Ioo, sub_zero, max_eq_left heps.le]
  simp only [smul_eq_mul, mul_one]
  ring

lemma principal_integrated_re_lower {N : ℕ} [NeZero N] :
    ∃ eps : ℝ, 0 < eps ∧ ∀ u : ℝ, 0 ≤ u → u < 1 →
      (totientRatio N / 4) ^ u * eps ^ (1 - u) / (1 - u) - eps ≤
        (integratedGeneratingValue (1 : DirichletCharacter ℂ N) u).re := by
  obtain ⟨eps, heps0, _heps1, hpoint⟩ := principal_generating_local_lower N
  refine ⟨eps, heps0, ?_⟩
  intro u hu0 hu1
  have hF := principalRealIntegrand_integrable (N := N) hu0 hu1
  have hFI : IntegrableOn (principalRealIntegrand N u) (Ioo 0 eps) := hF.mono_set Ioo_subset_Ioi_self
  have hp : IntegrableOn (fun t : ℝ => t ^ (-u)) (Ioo 0 eps) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff heps0).2 (by linarith)
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 eps) :=
    (continuous_const.integrableOn_Icc (a := (0 : ℝ)) (b := eps)).mono_set Ioo_subset_Icc_self
  rw [principal_integrated_re_eq_real_integral hu0 hu1, ← integral_abel_power_kernel hu1 heps0]
  calc
    _ ≤ ∫ t : ℝ in Ioo 0 eps, principalRealIntegrand N u t := by
      apply integral_mono_ae ((hp.const_mul _).sub hc) hFI
      apply ae_restrict_of_forall_mem measurableSet_Ioo
      intro t ht
      have h := hpoint u hu0 hu1.le t ht.1 ht.2.le
      have hratio : totientRatio N / (4 * t) = (totientRatio N / 4) / t := by ring
      have hk0 : (0 : ℝ) ≤ totientRatio N / 4 := div_nonneg (totientRatio_pos N).le (by norm_num)
      rw [hratio, Real.div_rpow hk0 ht.1.le, div_eq_mul_inv, ← Real.rpow_neg ht.1.le] at h
      exact sub_le_sub_right h 1
    _ ≤ _ := setIntegral_mono_set hF
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => principalRealIntegrand_nonneg hu0 hu1.le ht))
      (Eventually.of_forall (fun _ ht => ht.1))

/-- The principal character supplies the positive Abel lower bound φ(N)/(4N). -/
lemma principal_abel_lower_bound (N : ℕ) [NeZero N] :
    HasAbelLowerBound (fun u : ℝ => (1 - u) *
      (integratedGeneratingValue (1 : DirichletCharacter ℂ N) u).re) (totientRatio N / 4) := by
  obtain ⟨eps, heps, hlower⟩ := principal_integrated_re_lower (N := N)
  let g : ℝ → ℝ := fun u => (totientRatio N / 4) ^ u * eps ^ (1 - u) - (1 - u) * eps
  have hid : Tendsto (fun u : ℝ => u) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
  have hk : totientRatio N / 4 ≠ 0 := ne_of_gt (div_pos (totientRatio_pos N) (by norm_num))
  have hg : Tendsto g (𝓝[<] 1) (𝓝 (totientRatio N / 4)) := by
    have ha := (tendsto_const_nhds (x := totientRatio N / 4)).rpow hid (Or.inl hk)
    have hb := (tendsto_const_nhds (x := eps)).rpow
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hid) (Or.inl heps.ne')
    have hc := ((tendsto_const_nhds (x := (1 : ℝ))).sub hid).mul_const eps
    simpa only [g, sub_self, Real.rpow_zero, Real.rpow_one, mul_one, zero_mul, sub_zero] using (ha.mul hb).sub hc
  apply hasAbelLowerBound_of_tendsto_minorant hg
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with u hu
  have h := mul_le_mul_of_nonneg_left (hlower u hu.1.le hu.2) (sub_nonneg.mpr hu.2.le)
  have hne : 1 - u ≠ 0 := by linarith [hu.2]
  dsimp [g]
  convert h using 1
  field_simp

end Erdos143
