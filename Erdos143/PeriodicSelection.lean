import Erdos143.PeriodicMass
import Erdos143.FiniteExtraction

noncomputable section
open scoped BigOperators ENNReal

namespace Erdos143

/-- The sufficient periodic-selection lemma, now proved without an assumed analytic interface.
All quantifiers are in the intended order: the period and residue set are fixed first. -/
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

end Erdos143
