import Erdos143.PrincipalBound

noncomputable section
open Filter Complex
open scoped Topology BigOperators LSeries.notation

namespace Erdos143

def totientRatio (N : ℕ) : ℝ := (N.totient : ℝ) / N

lemma totientRatio_pos (N : ℕ) [NeZero N] : 0 < totientRatio N := by
  unfold totientRatio
  exact div_pos (by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos N))
    (by exact_mod_cast NeZero.pos N)

lemma principal_residue_eq_ratio (N : ℕ) [NeZero N] :
    (∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹)) = (totientRatio N : ℂ) := by
  have h : (N.totient : ℂ) = (N : ℂ) * ∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹) := by
    have h := congrArg (Rat.castHom ℂ) (Nat.totient_eq_mul_prod_factors N)
    simpa only [map_natCast, map_mul, map_prod, map_sub, map_one, map_inv₀] using h
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  calc
    _ = (N.totient : ℂ) / N := by
      apply (eq_div_iff hN).2
      simpa [mul_comm] using h.symm
    _ = (totientRatio N : ℂ) := by simp [totientRatio]

/-- The real one-sided principal-character residue, with the exact φ(N)/N constant. -/
lemma principal_norm_residue (N : ℕ) [NeZero N] :
    Tendsto (fun t : ℝ => t * ‖L ↗(1 : DirichletCharacter ℂ N) (1 + (t : ℂ))‖)
      (𝓝[>] 0) (𝓝 (totientRatio N)) := by
  have hcont : Continuous (fun t : ℝ => 1 + (t : ℂ)) := continuous_const.add continuous_ofReal
  have hmaps : Set.MapsTo (fun t : ℝ => 1 + (t : ℂ)) (Set.Ioi 0) ({1}ᶜ : Set ℂ) := by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro heq
    have hre := congrArg Complex.re heq
    simp only [add_re, one_re, ofReal_re] at hre
    have ht0 : 0 < t := ht
    linarith
  have hto : Tendsto (fun t : ℝ => 1 + (t : ℂ)) (𝓝[>] 0) (𝓝[≠] 1) := by
    simpa using (hcont.continuousWithinAt (x := 0) (s := Set.Ioi 0)).tendsto_nhdsWithin hmaps
  have hres := (DirichletCharacter.LFunctionTrivChar_residue_one (N := N)).comp hto
  rw [principal_residue_eq_ratio] at hres
  have hnorm := hres.norm
  rw [Complex.norm_of_nonneg (totientRatio_pos N).le] at hnorm
  apply hnorm.congr'
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  have hs : 1 < (1 + (t : ℂ)).re := by simpa using ht0
  simp only [Function.comp_apply, add_sub_cancel_left, norm_mul,
    Complex.norm_of_nonneg ht0.le, DirichletCharacter.LFunctionTrivChar,
    DirichletCharacter.LFunction_eq_LSeries _ hs]

lemma principal_local_bounds (N : ℕ) [NeZero N] :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧ ∀ t : ℝ, 0 < t → t ≤ eps →
      totientRatio N / (2 * t) ≤ ‖L ↗(1 : DirichletCharacter ℂ N) (1 + (t : ℂ))‖ ∧
      ‖L ↗(1 : DirichletCharacter ℂ N) (1 + (t : ℂ))‖ ≤ 2 * totientRatio N / t := by
  have hκ := totientRatio_pos N
  have hevent := (principal_norm_residue N).eventually
    (Ioo_mem_nhds (show totientRatio N / 2 < totientRatio N by linarith)
      (show totientRatio N < 2 * totientRatio N by linarith))
  obtain ⟨d, hd, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hevent
  refine ⟨min d 1, lt_min hd (by norm_num), min_le_right _ _, ?_⟩
  intro t ht hteps
  have htm : t * ‖L ↗(1 : DirichletCharacter ℂ N) (1 + (t : ℂ))‖ ∈
      Set.Ioo (totientRatio N / 2) (2 * totientRatio N) :=
    hsub ⟨ht, hteps.trans (min_le_left _ _)⟩
  constructor
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * t)).2
    nlinarith [htm.1]
  · apply (le_div_iff₀ ht).2
    nlinarith [htm.2]

lemma principal_generating_local_lower (N : ℕ) [NeZero N] :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ t : ℝ, 0 < t → t ≤ eps →
      (totientRatio N / (4 * t)) ^ u ≤
      ‖generatingValue (1 : DirichletCharacter ℂ N) (u : ℂ) (1 + (t : ℂ))‖ := by
  obtain ⟨eps, heps0, heps1, hbounds⟩ := principal_local_bounds N
  refine ⟨eps, heps0, heps1, ?_⟩
  intro u hu0 hu1 t ht hteps
  have hb := (hbounds t ht hteps).1
  have hdiv : totientRatio N / (4 * t) ≤
      ‖L ↗(1 : DirichletCharacter ℂ N) (1 + (t : ℂ))‖ / 2 := by
    calc
      _ = (totientRatio N / (2 * t)) / 2 := by field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_right hb (by norm_num)
  have hnonneg : (0 : ℝ) ≤ totientRatio N / (4 * t) :=
    div_nonneg (totientRatio_pos N).le (by positivity)
  have hpow := Real.rpow_le_rpow hnonneg hdiv hu0
  have h := principal_generatingValue_lower (N := N) hu0 hu1 (show (1 : ℝ) < 1 + t by linarith)
  simp only [Complex.ofReal_add, Complex.ofReal_one] at h
  exact hpow.trans h

/-- An integrable majorant t^(-u), with a constant uniform in the real Abel parameter. -/
lemma global_generating_local_upper :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ t : ℝ, 0 < t → t ≤ eps →
      ‖generatingValue (1 : DirichletCharacter ℂ 1) (u : ℂ) (1 + (t : ℂ))‖ ≤ 4 * t ^ (-u) := by
  obtain ⟨eps, heps0, heps1, hbounds⟩ := principal_local_bounds 1
  refine ⟨eps, heps0, heps1, ?_⟩
  intro u hu0 hu1 t ht hteps
  have hs : 1 < (1 + (t : ℂ)).re := by simpa using ht
  have hL : ‖L ↗(1 : DirichletCharacter ℂ 1) (1 + (t : ℂ))‖ ≤ 2 / t := by
    simpa [totientRatio] using (hbounds t ht hteps).2
  have hpow := Real.rpow_le_rpow (norm_nonneg _) hL hu0
  have h2 : (2 : ℝ) ^ u ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hu1
    simpa only [Real.rpow_one] using h
  calc
    _ ≤ 2 * ‖L ↗(1 : DirichletCharacter ℂ 1) (1 + (t : ℂ))‖ ^ u :=
      generatingValue_norm_le_two_rpow_LSeries _ hu0 hu1 hs
    _ ≤ 2 * (2 / t) ^ u := by linarith
    _ ≤ 4 * t ^ (-u) := by
      rw [Real.div_rpow (by norm_num) ht.le, Real.rpow_neg ht.le, div_eq_mul_inv]
      nlinarith [inv_nonneg.mpr (Real.rpow_nonneg ht.le u),
        mul_le_mul_of_nonneg_right h2 (inv_nonneg.mpr (Real.rpow_nonneg ht.le u))]

end Erdos143
