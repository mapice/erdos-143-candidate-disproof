import Erdos143.LayerDecomposition
import Erdos143.AbelBounds

noncomputable section
open Filter
open scoped Topology BigOperators

namespace Erdos143

lemma normalized_power_series_upper_of_tail {a : ℕ → ℝ} (ha : ∀ r, 0 ≤ a r)
    {c : ℝ} (hc : 0 ≤ c) (R : ℕ) (htail : ∀ r, R ≤ r → a r ≤ c)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hsum : Summable (fun r => u ^ r * a r)) :
    (1 - u) * (∑' r, u ^ r * a r) ≤ c + (1 - u) * ∑ r ∈ Finset.range R, a r := by
  let p : ℕ → ℝ := fun r => if r < R then a r else 0
  have hp0 : ∀ r ∉ Finset.range R, p r = 0 := by
    intro r hr
    simp only [Finset.mem_range] at hr
    simp [p, hr]
  have hpsum : Summable p := summable_of_ne_finset_zero hp0
  have hptsum : ∑' r, p r = ∑ r ∈ Finset.range R, a r := by
    rw [tsum_eq_sum hp0]
    apply Finset.sum_congr rfl
    intro r hr
    exact if_pos (Finset.mem_range.mp hr)
  have hg := (summable_geometric_of_lt_one hu0 hu1).mul_left c
  have hpoint (r : ℕ) : u ^ r * a r ≤ c * u ^ r + p r := by
    by_cases hr : r < R
    · have hpow : u ^ r ≤ 1 := pow_le_one₀ hu0 hu1.le
      have hm := mul_le_of_le_one_left (ha r) hpow
      have hc' := mul_nonneg hc (pow_nonneg hu0 r)
      simp only [p, if_pos hr]
      linarith
    · have h := mul_le_mul_of_nonneg_left (htail r (le_of_not_gt hr)) (pow_nonneg hu0 r)
      simpa only [p, if_neg hr, add_zero, mul_comm] using h
  have hle := hsum.tsum_le_tsum hpoint (hg.add hpsum)
  rw [Summable.tsum_add hg hpsum, tsum_mul_left, tsum_geometric_of_lt_one hu0 hu1, hptsum] at hle
  have h := mul_le_mul_of_nonneg_left hle (show 0 ≤ 1 - u by linarith)
  have hne : 1 - u ≠ 0 := by linarith
  calc
    _ ≤ (1 - u) * (c * (1 - u)⁻¹ + ∑ r ∈ Finset.range R, a r) := h
    _ = _ := by field_simp

/-- An Abel lower bound strictly above c forces arbitrarily high individual Ω layers
whose weight exceeds c. No claim about a limit of every individual layer is made. -/
lemma exists_large_layer_of_abel_lower (E : Set ℕ) {c d : ℝ} (hc : 0 ≤ c) (hcd : c < d)
    (hAbel : HasAbelLowerBound (fun u : ℝ => (1 - u) * setAbelMass E u) d) (R : ℕ) :
    ∃ r : ℕ, R ≤ r ∧ c < layerMass E r := by
  by_contra hnot
  have htail : ∀ r, R ≤ r → layerMass E r ≤ c := by
    intro r hr
    by_contra hgt
    exact hnot ⟨r, hr, lt_of_not_ge hgt⟩
  let K : ℝ := ∑ r ∈ Finset.range R, layerMass E r
  have hupper : ∀ᶠ u : ℝ in 𝓝[<] 1, (1 - u) * setAbelMass E u ≤ c + (1 - u) * K := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with u hu
    have hs := layer_abel_hasSum E hu.1.le hu.2
    have h := normalized_power_series_upper_of_tail (layerMass_nonneg E) hc R htail hu.1.le hu.2 hs.summable
    rwa [hs.tsum_eq] at h
  have hid : Tendsto (fun u : ℝ => u) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
  have hlim : Tendsto (fun u : ℝ => c + (1 - u) * K) (𝓝[<] 1) (𝓝 c) := by
    simpa using (tendsto_const_nhds (x := c)).add (((tendsto_const_nhds (x := (1 : ℝ))).sub hid).mul_const K)
  have hm1 : c < (c + d) / 2 := by linarith
  have hm2 : (c + d) / 2 < d := by linarith
  obtain ⟨u, hu, hl, hh⟩ := (hupper.and ((hAbel ((c + d) / 2) hm2).and
    (hlim.eventually (eventually_lt_nhds hm1)))).exists
  linarith

end Erdos143
