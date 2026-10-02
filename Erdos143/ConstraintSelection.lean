import Erdos143.FiniteDensity
import Erdos143.PeriodicSelection

noncomputable section
open scoped BigOperators ENNReal
namespace Erdos143

/-- Finitely many residue exclusions with total forbidden density below one third
admit an arbitrarily far-out finite primitive set of logarithmic weight above one sixth.
No independence of the residue conditions is required. -/
lemma finite_constraints_primitive_selection {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (hm : ∀ i, 0 < m i) (B : (i : ι) → Finset (ZMod (m i)))
    (hbudget : (∑ i, ((B i).card : ℚ) / m i) < 1 / 3)
    (N : ℕ) (hN : 2 ≤ N) :
    ∃ P : Finset ℕ, (∀ n ∈ P, N ≤ n ∧ ∀ i, (n : ZMod (m i)) ∉ B i) ∧
      Primitive (P : Set ℕ) ∧ (1 / 6 : ℝ≥0∞) < ∑ n ∈ P, weight n := by
  classical
  let L := ∏ i, m i
  have hL : 0 < L := Finset.prod_pos (fun i _ => hm i)
  letI : NeZero L := ⟨ne_of_gt hL⟩
  letI (i : ι) : NeZero (m i) := ⟨ne_of_gt (hm i)⟩
  have hdvd (i : ι) : m i ∣ L := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  let C (i : ι) : Finset (ZMod L) :=
    Finset.univ.filter (fun x => ZMod.castHom (hdvd i) (ZMod (m i)) x ∈ B i)
  let S : Finset (ZMod L) := (Finset.univ.biUnion C)ᶜ
  have hden (i : ι) : ((C i).card : ℚ) / L = ((B i).card : ℚ) / m i :=
    zmod_preimage_density (hdvd i) (B i)
  have hS : (2 / 3 : ℚ) < (S.card : ℚ) / L := by
    have h := complement_union_density (Finset.univ : Finset ι) C
    simp only [ZMod.card, hden] at h
    change 1 - (∑ i, ((B i).card : ℚ) / m i) ≤ (S.card : ℚ) / L at h
    linarith
  have hSR : (2 / 3 : ℝ) < (S.card : ℝ) / L := by
    have hcast := Rat.cast_lt (K := ℝ) |>.mpr hS
    push_cast at hcast
    exact hcast
  obtain ⟨P, hP, hprim, hw⟩ := periodic_primitive_selection L S hSR N hN
  refine ⟨P, ?_, hprim, hw⟩
  intro n hn
  refine ⟨(hP n hn).1, ?_⟩
  intro i hi
  have hout : (n : ZMod L) ∉ Finset.univ.biUnion C := Finset.mem_compl.mp (hP n hn).2
  apply hout
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  change (n : ZMod L) ∈ Finset.univ.filter _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_natCast]
  exact hi

end Erdos143
