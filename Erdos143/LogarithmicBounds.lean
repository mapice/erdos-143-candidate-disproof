import Erdos143.LogarithmicEulerProduct
import Erdos143.PrincipalResidue

noncomputable section
open Complex
open scoped Topology LSeries.notation

namespace Erdos143.Logarithmic

/-- A named interface for the uniform logarithmic correction proved by the Taylor series. -/
def RemainderBound : Prop :=
  ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) {u : ℝ}, 0 ≤ u → u ≤ 1 →
    ∀ {s : ℂ}, 1 < s.re →
      ‖logarithmicEulerRemainder (fun p : Nat.Primes => χ p * (p : ℂ) ^ (-s)) u‖ ≤ 1 - u

namespace Bounds

lemma generating_norm_eq_exp_remainder {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    ‖generatingValue χ (u : ℂ) s‖ =
      ‖L ↗χ s‖ ^ u * Real.exp
        (logarithmicEulerRemainder (fun p : Nat.Primes => χ p * (p : ℂ) ^ (-s)) u).re := by
  have hF := norm_pos_iff.mpr (generatingValue_ne_zero_logarithmic χ hu0 hu1 hs)
  have hL := norm_pos_iff.mpr (LSeries_ne_zero_logarithmic χ hs)
  rw [← Real.exp_log hF, generatingValue_logarithmic_identity χ hu0 hu1 hs,
    Real.exp_add, Real.rpow_def_of_pos hL, mul_comm u]

lemma generating_norm_upper (hR : RemainderBound) {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    ‖generatingValue χ (u : ℂ) s‖ ≤ Real.exp 1 * ‖L ↗χ s‖ ^ u := by
  rw [generating_norm_eq_exp_remainder χ hu0 hu1 hs]
  have hr := (Complex.re_le_norm _).trans (hR χ hu0 hu1 hs)
  have he := Real.exp_le_exp.mpr (hr.trans (by linarith : 1 - u ≤ 1))
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left he (Real.rpow_nonneg (norm_nonneg (L ↗χ s)) u)

lemma generating_norm_lower (hR : RemainderBound) {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 1 / 2 ≤ u) (hu1 : u ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    (1 / 2 : ℝ) * ‖L ↗χ s‖ ^ u ≤ ‖generatingValue χ (u : ℂ) s‖ := by
  have hu0' : 0 ≤ u := by linarith
  rw [generating_norm_eq_exp_remainder χ hu0' hu1 hs]
  have hr := ((abs_le.mp (Complex.abs_re_le_norm _)).1).trans' (neg_le_neg (hR χ hu0' hu1 hs))
  have he := Real.add_one_le_exp
    (logarithmicEulerRemainder (fun p : Nat.Primes => χ p * (p : ℂ) ^ (-s)) u).re
  have he' : (1 / 2 : ℝ) ≤ Real.exp
      (logarithmicEulerRemainder (fun p : Nat.Primes => χ p * (p : ℂ) ^ (-s)) u).re := by
    linarith
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left he' (Real.rpow_nonneg (norm_nonneg (L ↗χ s)) u)

lemma nonprincipal_generatingValue_bounded (hR : RemainderBound) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖generatingValue χ (u : ℂ) (1 + (t : ℂ))‖ ≤ C := by
  have hcont : Continuous (fun t : ℝ => χ.LFunction (1 + (t : ℂ))) :=
    (nonprincipal_LFunction_continuous χ hχ).comp (continuous_const.add Complex.continuous_ofReal)
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hcont.continuousOn
  let K : ℝ := max 1 B
  have hK : 1 ≤ K := le_max_left _ _
  refine ⟨Real.exp 1 * K, mul_pos (Real.exp_pos _) (by linarith), ?_⟩
  intro u hu0 hu1 t ht0 ht1
  have hs : 1 < (1 + (t : ℂ)).re := by simpa using ht0
  have hL : ‖L ↗χ (1 + (t : ℂ))‖ ≤ K := by
    rw [← χ.LFunction_eq_LSeries hs]
    exact (hB t ⟨ht0.le, ht1⟩).trans (le_max_right _ _)
  have hpow : ‖L ↗χ (1 + (t : ℂ))‖ ^ u ≤ K := by
    calc
      _ ≤ K ^ u := Real.rpow_le_rpow (norm_nonneg _) hL hu0
      _ ≤ K ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK hu1
      _ = K := Real.rpow_one _
  exact (generating_norm_upper hR χ hu0 hu1 hs).trans
    (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le)

lemma principal_generating_local_lower (hR : RemainderBound) (N : ℕ) [NeZero N] :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧ ∀ u : ℝ, 1 / 2 ≤ u → u ≤ 1 →
      ∀ t : ℝ, 0 < t → t ≤ eps →
      (1 / 2 : ℝ) * (totientRatio N / (2 * t)) ^ u ≤
        ‖generatingValue (1 : DirichletCharacter ℂ N) (u : ℂ) (1 + (t : ℂ))‖ := by
  obtain ⟨eps, heps0, heps1, hbounds⟩ := principal_local_bounds N
  refine ⟨eps, heps0, heps1, ?_⟩
  intro u hu0 hu1 t ht hteps
  have hs : 1 < (1 + (t : ℂ)).re := by simpa using ht
  have hp := Real.rpow_le_rpow (div_nonneg (totientRatio_pos N).le (by positivity) : (0 : ℝ) ≤ totientRatio N / (2 * t))
    (hbounds t ht hteps).1 (by linarith : 0 ≤ u)
  exact (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans
    (generating_norm_lower hR _ hu0 hu1 hs)

lemma global_generating_local_upper (hR : RemainderBound) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ t : ℝ, 0 < t → t ≤ eps →
      ‖generatingValue (1 : DirichletCharacter ℂ 1) (u : ℂ) (1 + (t : ℂ))‖ ≤
        (2 * Real.exp 1) * t ^ (-u) := by
  obtain ⟨eps, heps0, heps1, hbounds⟩ := principal_local_bounds 1
  refine ⟨eps, heps0, heps1, ?_⟩
  intro u hu0 hu1 t ht hteps
  have hs : 1 < (1 + (t : ℂ)).re := by simpa using ht
  have hL : ‖L ↗(1 : DirichletCharacter ℂ 1) (1 + (t : ℂ))‖ ≤ 2 / t := by
    simpa [totientRatio] using (hbounds t ht hteps).2
  have hpow := Real.rpow_le_rpow (norm_nonneg _) hL hu0
  have h2 : (2 : ℝ) ^ u ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hu1
  calc
    _ ≤ Real.exp 1 * ‖L ↗(1 : DirichletCharacter ℂ 1) (1 + (t : ℂ))‖ ^ u :=
      generating_norm_upper hR _ hu0 hu1 hs
    _ ≤ Real.exp 1 * (2 / t) ^ u :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ ≤ _ := by
      rw [Real.div_rpow (by norm_num) ht.le, Real.rpow_neg ht.le, div_eq_mul_inv]
      nlinarith [mul_le_mul_of_nonneg_right h2 (inv_nonneg.mpr (Real.rpow_nonneg ht.le u)),
        Real.exp_pos (1 : ℝ)]

end Bounds

end Erdos143.Logarithmic
