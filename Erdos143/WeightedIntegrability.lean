import Erdos143.GeneratingIntegrability
import Erdos143.PositiveInterchange
import Erdos143.MellinWeight

noncomputable section
open MeasureTheory Set Complex
open scoped ArithmeticFunction.Omega

namespace Erdos143

def realGeneratingTailTerm (u : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  u ^ Ω (n + 2) * ((n : ℝ) + 2) ^ (-(1 + t))

lemma realGeneratingTailTerm_nonneg {u : ℝ} (hu : 0 ≤ u) (n : ℕ) (t : ℝ) :
    0 ≤ realGeneratingTailTerm u n t := by unfold realGeneratingTailTerm; positivity

lemma realGeneratingTailTerm_integrable (u : ℝ) (n : ℕ) :
    IntegrableOn (realGeneratingTailTerm u n) (Ioi 0) := by
  exact (weight_integrand_integrable (by linarith [Nat.cast_nonneg (α := ℝ) n] : (1 : ℝ) < n + 2)).const_mul _

lemma integral_realGeneratingTailTerm (u : ℝ) (n : ℕ) :
    (∫ t : ℝ in Ioi 0, realGeneratingTailTerm u n t) =
      u ^ Ω (n + 2) / (((n : ℝ) + 2) * Real.log ((n : ℝ) + 2)) := by
  unfold realGeneratingTailTerm
  rw [integral_const_mul, real_weight_integral (by linarith [Nat.cast_nonneg (α := ℝ) n] : (1 : ℝ) < n + 2)]
  ring

lemma realGeneratingTailTerm_summable {u t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ht : 0 < t) :
    Summable (fun n => realGeneratingTailTerm u n t) := by
  have hs : (1 : ℝ) < 1 + t := by linarith
  have h := (principalGeneratingTerm_summable (N := 1) hu0 hu1 hs).comp_injective
    (fun m n (h : m + 2 = n + 2) => by omega)
  simpa only [Function.comp_def, principalGeneratingTerm_mod_one, realGeneratingTailTerm, Nat.cast_add, Nat.cast_ofNat] using h

lemma global_sub_one_norm_eq_real_tail {u t : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ht : 0 < t) :
    ‖generatingValue (1 : DirichletCharacter ℂ 1) (u : ℂ) (1 + (t : ℂ)) - 1‖ =
      ∑' n : ℕ, realGeneratingTailTerm u n t := by
  have hu : ‖(u : ℂ)‖ ≤ 1 := by rw [Complex.norm_of_nonneg hu0]; exact hu1
  have hsC : 1 < (1 + (t : ℂ)).re := by simpa using ht
  rw [generatingValue_sub_one_eq_tail _ hu hsC]
  have hterm (n : ℕ) : generatingSummandHom (1 : DirichletCharacter ℂ 1) (u : ℂ)
      (ne_zero_of_one_lt_re hsC) (n + 2) = (realGeneratingTailTerm u n t : ℂ) := by
    have h := principalGeneratingTerm_cast (N := 1) (u := u) (show (1 : ℝ) < 1 + t by linarith) (n + 2)
    simpa only [ofReal_add, ofReal_one, principalGeneratingTerm_mod_one, realGeneratingTailTerm,
      Nat.cast_add, Nat.cast_ofNat] using h
  simp only [hterm, ← Complex.ofReal_tsum]
  exact Complex.norm_of_nonneg (tsum_nonneg (realGeneratingTailTerm_nonneg hu0 · t))

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

end Erdos143
