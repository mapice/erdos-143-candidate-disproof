import Erdos143.GeneratingEulerProducts
import Mathlib.NumberTheory.LSeries.Deriv

noncomputable section
open Complex
open scoped Topology LSeries.notation

namespace Erdos143

def generatingCoefficient {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℂ) (n : ℕ) : ℂ :=
  omegaWeightHom u n * χ n

lemma generatingValue_eq_LSeries {N : ℕ} (χ : DirichletCharacter ℂ N) (u s : ℂ) :
    generatingValue χ u s = LSeries (generatingCoefficient χ u) s := by
  unfold generatingValue LSeries
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn, LSeries.term_zero]
  · simp only [LSeries.term_of_ne_zero hn, generatingCoefficient, div_eq_mul_inv, cpow_neg]
    ring

lemma generatingCoefficient_norm_le_one {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℂ} (hu : ‖u‖ ≤ 1) (n : ℕ) : ‖generatingCoefficient χ u n‖ ≤ 1 := by
  unfold generatingCoefficient
  rw [norm_mul]
  simpa using mul_le_mul (omegaWeightHom_norm_le_one hu n) (χ.norm_le_one n)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

lemma generatingCoefficient_abscissa_le_one {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℂ} (hu : ‖u‖ ≤ 1) : LSeries.abscissaOfAbsConv (generatingCoefficient χ u) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => generatingCoefficient_norm_le_one χ hu n⟩

/-- Ordinary continuity in the exponent away from the boundary s=1. -/
lemma generatingValue_continuousAt {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u s : ℂ} (hu : ‖u‖ ≤ 1) (hs : 1 < s.re) :
    ContinuousAt (generatingValue χ u) s := by
  have h := generatingCoefficient_abscissa_le_one χ hu
  have hs' : (1 : EReal) < (s.re : EReal) := by exact_mod_cast hs
  have heq : generatingValue χ u = LSeries (generatingCoefficient χ u) := by
    funext z
    exact generatingValue_eq_LSeries χ u z
  rw [heq]
  exact (LSeries_hasDerivAt (h.trans_lt hs')).continuousAt

lemma generatingValue_continuousOn_positive {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℂ} (hu : ‖u‖ ≤ 1) :
    ContinuousOn (fun t : ℝ => generatingValue χ u (1 + (t : ℂ))) (Set.Ioi 0) := by
  intro t ht
  have hs : 1 < (1 + (t : ℂ)).re := by simpa using ht
  have hinner : ContinuousAt (fun x : ℝ => 1 + (x : ℂ)) t :=
    (continuous_const.add continuous_ofReal).continuousAt
  exact (ContinuousAt.comp (f := fun x : ℝ => 1 + (x : ℂ)) (x := t)
    (generatingValue_continuousAt χ hu hs) hinner).continuousWithinAt

end Erdos143
