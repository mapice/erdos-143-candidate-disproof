import Erdos143.GeneratingRegularity
import Mathlib.Analysis.PSeries

noncomputable section
open Complex
open scoped BigOperators

namespace Erdos143

lemma generatingSummand_norm_le_rpow {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℂ} (hu : ‖u‖ ≤ 1) {s : ℝ} (hs : 1 < s) (n : ℕ) :
    ‖generatingSummandHom χ u (ne_zero_of_one_lt_re (show 1 < (s : ℂ).re by simpa using hs)) n‖ ≤
      (n : ℝ) ^ (-s) := by
  have hsC : 1 < (s : ℂ).re := by simpa using hs
  have hid : generatingSummandHom χ u (ne_zero_of_one_lt_re hsC) n =
      generatingCoefficient χ u n * (n : ℂ) ^ (-(s : ℂ)) := by
    simp only [generatingSummandHom, generatingCoefficient, dirichletSummandHom,
      MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
    ring
  rw [hid, norm_mul]
  have hnorm : ‖(n : ℂ) ^ (-(s : ℂ))‖ = (n : ℝ) ^ (-s) := by
    rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n)
      (re_neg_ne_zero_of_one_lt_re hsC), neg_re, ofReal_re]
  rw [hnorm]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (generatingCoefficient_norm_le_one χ hu n)

lemma generatingValue_sub_one_eq_tail {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u s : ℂ} (hu : ‖u‖ ≤ 1) (hs : 1 < s.re) :
    generatingValue χ u s - 1 =
      ∑' n : ℕ, generatingSummandHom χ u (ne_zero_of_one_lt_re hs) (n + 2) := by
  have hsum := (generatingSummand_norm_summable χ hu hs).of_norm
  have h := hsum.sum_add_tsum_nat_add 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, map_zero, map_one, zero_add] at h
  rw [generatingValue_eq_tsum χ u (ne_zero_of_one_lt_re hs)]
  exact (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h)).symm

lemma shifted_square_reciprocal_summable :
    Summable (fun n : ℕ => (((n : ℝ) + 2) ^ 2)⁻¹) := by
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := Real.summable_nat_pow_inv.mpr (by decide)
  simpa only [Nat.cast_add, Nat.cast_ofNat] using (summable_nat_add_iff 2).2 h

def tailMajorantConst : ℝ := 2 * ∑' n : ℕ, (((n : ℝ) + 2) ^ 2)⁻¹

lemma tailMajorantConst_nonneg : 0 ≤ tailMajorantConst := by
  unfold tailMajorantConst
  positivity

lemma rpow_tail_comparison {x t : ℝ} (hx : 2 ≤ x) (ht : 1 ≤ t) :
    x ^ (-(1 + t)) ≤ (x ^ 2)⁻¹ * (2 : ℝ) ^ (-(t - 1)) := by
  have hx0 : 0 < x := by linarith
  have hexp : -(1 + t) = (-2 : ℝ) + -(t - 1) := by ring
  rw [hexp, Real.rpow_add hx0, Real.rpow_neg hx0.le, Real.rpow_two]
  have hpow := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 2) hx
    (show -(t - 1) ≤ 0 by linarith)
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

lemma two_rpow_tail_eq_exp (t : ℝ) :
    (2 : ℝ) ^ (-(t - 1)) = 2 * Real.exp ((-Real.log 2) * t) := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  calc
    Real.exp (Real.log 2 * -(t - 1)) = Real.exp (Real.log 2 + (-Real.log 2) * t) := by
      congr 1
      ring
    _ = _ := by rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- Uniform exponential decay of G−1 for large t, for every character and every |u|≤1. -/
lemma generatingValue_tail_bound {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℂ} (hu : ‖u‖ ≤ 1) {t : ℝ} (ht : 1 ≤ t) :
    ‖generatingValue χ u (1 + (t : ℂ)) - 1‖ ≤
      tailMajorantConst * Real.exp ((-Real.log 2) * t) := by
  have hs : (1 : ℝ) < 1 + t := by linarith
  have hsC : 1 < (1 + (t : ℂ)).re := by simpa using hs
  let f : ℕ → ℂ := fun n => generatingSummandHom χ u (ne_zero_of_one_lt_re hsC) (n + 2)
  have hsum : Summable (fun n => ‖f n‖) :=
    (generatingSummand_norm_summable χ hu hsC).comp_injective (fun _ _ h => by omega)
  have hpoint (n : ℕ) : ‖f n‖ ≤ (((n : ℝ) + 2) ^ 2)⁻¹ * (2 : ℝ) ^ (-(t - 1)) := by
    have h := generatingSummand_norm_le_rpow χ hu hs (n + 2)
    simp only [ofReal_add, ofReal_one, Nat.cast_add, Nat.cast_ofNat] at h
    exact h.trans (rpow_tail_comparison (by linarith [Nat.cast_nonneg (α := ℝ) n] : (2 : ℝ) ≤ (n : ℝ) + 2) ht)
  rw [generatingValue_sub_one_eq_tail χ hu hsC]
  calc
    ‖∑' n, f n‖ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n : ℕ, (((n : ℝ) + 2) ^ 2)⁻¹ * (2 : ℝ) ^ (-(t - 1)) :=
      hsum.tsum_le_tsum hpoint (shifted_square_reciprocal_summable.mul_right _)
    _ = tailMajorantConst * Real.exp ((-Real.log 2) * t) := by
      rw [tsum_mul_right, two_rpow_tail_eq_exp]
      unfold tailMajorantConst
      ring

end Erdos143
