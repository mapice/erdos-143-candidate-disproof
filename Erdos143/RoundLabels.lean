import Erdos143.ConstraintSelection
import Erdos143.RootResidues

noncomputable section
open scoped BigOperators ENNReal
namespace Erdos143

/-- The exact finite-round union bound, using the private-prime filter and one
short forbidden-residue interval for each already inserted root. -/
lemma round_labels (H R : Finset ℕ) (D N : ℕ)
    (hH : ∀ h ∈ H, 0 < h) (hD : 0 < D) (hR : ∀ p ∈ R, D ≤ p)
    (hbudget : (∑ h ∈ H, (1 : ℚ) / h) < 1 / 100)
    (hcard : R.card ≤ D / 12) (hN : 2 ≤ N) :
    ∃ P : Finset ℕ,
      (∀ n ∈ P, N ≤ n ∧ (∀ h ∈ H, ¬ h ∣ n) ∧
        ∀ p ∈ R, (n : ZMod p) ∉ rootBadResidues p D) ∧
      Primitive (P : Set ℕ) ∧ (1 / 6 : ℝ≥0∞) < ∑ n ∈ P, weight n := by
  classical
  let m : (H ⊕ R) → ℕ := Sum.elim Subtype.val Subtype.val
  let B : (i : H ⊕ R) → Finset (ZMod (m i)) := fun i =>
    match i with
    | Sum.inl _ => {0}
    | Sum.inr p => rootBadResidues p D
  have hm (i : H ⊕ R) : 0 < m i := by
    cases i with
    | inl h => exact hH h h.property
    | inr p => exact lt_of_lt_of_le hD (hR p p.property)
  have hroots : (∑ p ∈ R, ((rootBadResidues p D).card : ℚ) / p) ≤ 1 / 4 := by
    have hsum := Finset.sum_le_sum (s := R) (fun p hp => rootBadResidues_density hD (hR p hp))
    have hc : (R.card : ℚ) * 12 ≤ D := by
      have : R.card * 12 ≤ D := (Nat.mul_le_mul_right 12 hcard).trans (Nat.div_mul_le_self D 12)
      exact_mod_cast this
    have hD' : (0 : ℚ) < D := Nat.cast_pos.mpr hD
    simp only [Finset.sum_const, nsmul_eq_mul] at hsum
    have hmul : (R.card : ℚ) * (3 / D) ≤ 1 / 4 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 4)).mpr
      field_simp
      nlinarith
    exact hsum.trans hmul
  have hb : (∑ i, ((B i).card : ℚ) / m i) < 1 / 3 := by
    simp only [Fintype.sum_sum_type, B, m, Sum.elim_inl, Sum.elim_inr,
      Finset.card_singleton, Nat.cast_one]
    rw [Finset.sum_coe_sort H (fun h => (1 : ℚ) / h),
      Finset.sum_coe_sort R (fun p => ((rootBadResidues p D).card : ℚ) / p)]
    linarith
  obtain ⟨P, hP, hprim, hw⟩ := finite_constraints_primitive_selection m hm B hb N hN
  refine ⟨P, ?_, hprim, hw⟩
  intro n hn
  refine ⟨(hP n hn).1, ?_, ?_⟩
  · intro h hh hdvd
    have hnot := (hP n hn).2 (Sum.inl ⟨h, hh⟩)
    apply hnot
    change (n : ZMod h) ∈ ({0} : Finset (ZMod h))
    simp only [Finset.mem_singleton]
    exact (ZMod.natCast_eq_zero_iff n h).mpr hdvd
  · intro p hp
    exact (hP n hn).2 (Sum.inr ⟨p, hp⟩)

end Erdos143
