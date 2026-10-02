import Erdos143.GeneratingDomination
import Erdos143.PrincipalResidue
import Erdos143.ImproperControl

noncomputable section
open MeasureTheory Set

namespace Erdos143

/-- Absolute integrability of the subtracted generating function for each real 0≤u<1. -/
lemma generatingValue_sub_one_integrable {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    IntegrableOn (fun t : ℝ => generatingValue χ (u : ℂ) (1 + (t : ℂ)) - 1) (Ioi 0) := by
  have hu : ‖(u : ℂ)‖ ≤ 1 := by rw [Complex.norm_of_nonneg hu0]; exact hu1.le
  have hcont := (generatingValue_continuousOn_positive χ hu).sub (continuousOn_const (c := (1 : ℂ)))
  obtain ⟨eps, heps0, heps1, hsmall⟩ := global_generating_local_upper
  apply integrableOn_Ioi_of_power_exp_bounds hcont heps0 heps1
    (show -1 < -u by linarith) (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    (C := 4) (D := 1) (E := tailMajorantConst)
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

/-- For a nonprincipal character the endpoint u=1 is also integrable, using the uniform
boundedness proved directly from L-function continuity. -/
lemma nonprincipal_generatingValue_sub_one_integrable {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    IntegrableOn (fun t : ℝ => generatingValue χ (u : ℂ) (1 + (t : ℂ)) - 1) (Ioi 0) := by
  have hu : ‖(u : ℂ)‖ ≤ 1 := by rw [Complex.norm_of_nonneg hu0]; exact hu1
  have hcont := (generatingValue_continuousOn_positive χ hu).sub (continuousOn_const (c := (1 : ℂ)))
  obtain ⟨C, _hC0, hC⟩ := nonprincipal_generatingValue_bounded χ hχ
  apply integrableOn_Ioi_of_power_exp_bounds hcont (eps := 1) (by norm_num) (by norm_num)
    (a := 0) (by norm_num) (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    (C := 0) (D := C + 1) (E := tailMajorantConst)
  · intro t ht ht1
    have hb := hC u hu0 hu1 t ht ht1
    have hnorm := norm_sub_le (generatingValue χ (u : ℂ) (1 + (t : ℂ))) (1 : ℂ)
    simp only [norm_one] at hnorm
    simp only [Real.rpow_zero, mul_one, zero_add]
    linarith
  · intro t ht
    exact generatingValue_tail_bound χ hu ht

/-- The integrated generating function used by the Abel proof. -/
def integratedGeneratingValue {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℝ) : ℂ :=
  ∫ t : ℝ in Ioi 0, generatingValue χ (u : ℂ) (1 + (t : ℂ)) - 1

end Erdos143
