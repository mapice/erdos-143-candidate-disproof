import Erdos143.Progressions
import Erdos143.LogShift

noncomputable section
open scoped ArithmeticFunction.Omega

namespace Erdos143

def shiftPenalty (g : ℕ) : ℝ := (Real.log g / (g : ℝ)) * ∑' n, momentWeight n

lemma progressionTerm_scale_lower {g M c n : ℕ} (hg : 1 ≤ g)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (u ^ Ω g / (g : ℝ)) * progressionTerm M (c : ZMod M) u n -
      (Real.log g / (g : ℝ)) * momentWeight n ≤
      progressionTerm (g * M) ((g * c : ℕ) : ZMod (g * M)) u (g * n) := by
  by_cases hmod : (n : ZMod M) = (c : ZMod M)
  · have hnat := (ZMod.natCast_eq_natCast_iff n c M).mp hmod
    have hscaled : ((g * n : ℕ) : ZMod (g * M)) = ((g * c : ℕ) : ZMod (g * M)) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hnat.mul_left' g)
    simpa only [progressionTerm, if_pos hmod, if_pos hscaled] using realAbelTerm_mul_lower (m := n) hg hu0 hu1
  · have hlg : 0 ≤ Real.log (g : ℝ) := Real.log_nonneg (by exact_mod_cast hg)
    have hp : 0 ≤ (Real.log g / (g : ℝ)) * momentWeight n :=
      mul_nonneg (div_nonneg hlg (Nat.cast_nonneg _)) (momentWeight_nonneg n)
    calc
      _ = -(Real.log g / (g : ℝ)) * momentWeight n := by simp [progressionTerm, hmod]
      _ ≤ 0 := by nlinarith
      _ ≤ _ := progressionTerm_nonneg _ hu0 _

/-- Multiplication by g gives a subset of the required residue class. The loss is bounded
by one fixed, proved finite logarithmic moment, uniformly in 0≤u<1. -/
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

end Erdos143
