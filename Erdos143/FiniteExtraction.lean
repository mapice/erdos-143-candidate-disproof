import Erdos143.AbelLayerSelection

noncomputable section
open Filter
open scoped Topology BigOperators ArithmeticFunction.Omega

namespace Erdos143

/-- Extract a genuinely finite primitive set from one convergent positive Ω layer. -/
lemma finite_primitive_from_layer (E : Set ℕ) {r N : ℕ} (hr : 0 < r) (hNr : N ≤ r)
    {c : ℝ} (hc : c < layerMass E r) :
    ∃ P : Finset ℕ, (∀ n ∈ P, N ≤ n ∧ n ∈ E) ∧ Primitive (P : Set ℕ) ∧
      c < ∑ n ∈ P, natWeight n := by
  classical
  let f : ℕ → ℝ := fun n => if Ω n = r ∧ n ∈ E then natWeight n else 0
  have hsum : HasSum f (layerMass E r) := by
    rw [layerMass_eq_tsum_conditional]
    exact (layer_weight_summable E r).hasSum
  change Tendsto (fun T : Finset ℕ => ∑ n ∈ T, f n) atTop (𝓝 (layerMass E r)) at hsum
  obtain ⟨T, hT⟩ := (hsum.eventually (eventually_gt_nhds hc)).exists
  let P := T.filter (fun n => Ω n = r ∧ n ∈ E)
  have hP : ∀ n ∈ P, Ω n = r ∧ n ∈ E := fun n hn => (Finset.mem_filter.mp hn).2
  refine ⟨P, ?_, ?_, ?_⟩
  · intro n hn
    refine ⟨?_, (hP n hn).2⟩
    calc
      N ≤ r := hNr
      _ = Ω n := (hP n hn).1.symm
      _ ≤ n := omega_le_self n
  · exact primitive_of_constant_omega hr (fun n hn => (hP n hn).1)
  · simpa only [P, Finset.sum_filter, f] using hT

end Erdos143
