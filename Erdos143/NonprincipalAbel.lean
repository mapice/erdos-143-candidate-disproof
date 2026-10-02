import Erdos143.GeneratingIntegrability

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace Erdos143

/-- The character integrals stay bounded uniformly in the real Abel parameter, including u=1. -/
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

end Erdos143
