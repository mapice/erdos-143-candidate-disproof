import Erdos143.AllResiduesAbel
import Erdos143.LayerDecomposition

noncomputable section
open Filter
open scoped BigOperators Topology

namespace Erdos143

def periodicResidueSet (L : ℕ) (S : Finset (ZMod L)) : Set ℕ := {n | (n : ZMod L) ∈ S}

lemma setAbelMass_periodic (L : ℕ) (S : Finset (ZMod L)) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) :
    setAbelMass (periodicResidueSet L S) u = ∑ b ∈ S, progressionMass L b u := by
  classical
  have hterm (n : ℕ) : (periodicResidueSet L S).indicator (realAbelTerm u) n =
      ∑ b ∈ S, progressionTerm L b u n := by
    simp [periodicResidueSet, progressionTerm, Set.indicator_apply]
  unfold setAbelMass
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun b _ => progressionTerm_summable b hu0 hu1)]
  rfl

/-- A fixed periodic set has an Abel lower bound proportional to all its residue classes. -/
lemma periodic_abel_lower_bound (L : ℕ) [NeZero L] (S : Finset (ZMod L)) :
    HasAbelLowerBound (fun u : ℝ => (1 - u) * setAbelMass (periodicResidueSet L S) u)
      ((S.card : ℝ) / (4 * (L : ℝ))) := by
  have h := HasAbelLowerBound.sum S (fun b _ => all_residues_abel_lower_bound L b)
  have hconstant : (∑ _b ∈ S, (1 / (4 * (L : ℝ)))) = (S.card : ℝ) / (4 * (L : ℝ)) := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  rw [hconstant] at h
  apply h.mono
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with u hu
  rw [setAbelMass_periodic L S hu.1.le hu.2, Finset.mul_sum]

end Erdos143
