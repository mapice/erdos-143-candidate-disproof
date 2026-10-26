import Erdos143.LogarithmicEulerProduct
import Erdos143.LogarithmicRemainder

noncomputable section
open scoped BigOperators Topology

namespace Erdos143

/-- A term of the logarithmic Euler remainder, starting at Taylor degree two. -/
def logarithmicEulerTaylorTerm (u : ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  (((u : ℂ) ^ (n + 2) - (u : ℂ)) * z ^ (n + 2)) / ((n + 2 : ℕ) : ℂ)

/-- The absolute Taylor series of one Euler correction has the same geometric majorant. -/
lemma logarithmicEulerTaylorTerm_norm_tsum_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    (∑' n, ‖logarithmicEulerTaylorTerm u z n‖) ≤
      (1 - u) * (‖z‖ ^ 2 / (1 - ‖z‖)) := by
  have hf := (hasSum_logarithmicEulerFactorRemainder hu0 hu1 hz).summable.norm
  have hg := (hasSum_geometric_of_lt_one (norm_nonneg z) hz).mul_left
    ((1 - u) * ‖z‖ ^ 2)
  calc
    _ ≤ ∑' n, (1 - u) * ‖z‖ ^ 2 * ‖z‖ ^ n :=
      Summable.tsum_le_tsum (logarithmicEulerFactorRemainder_term_bound hu0 hu1 z)
        hf hg.summable
    _ = (1 - u) * (‖z‖ ^ 2 / (1 - ‖z‖)) := by
      rw [hg.tsum_eq]
      simp only [div_eq_mul_inv, mul_assoc]

/-- The remainder defined through local logarithms is exactly the iterated Taylor series. -/
lemma logarithmicEulerRemainder_eq_tsum_tsum {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (z : Nat.Primes → ℂ) (hz : ∀ p, ‖z p‖ ≤ (p : ℝ)⁻¹) :
    logarithmicEulerRemainder z u = ∑' p, ∑' n, logarithmicEulerTaylorTerm u (z p) n := by
  unfold logarithmicEulerRemainder
  apply tsum_congr
  intro p
  have hhalf := (hz p).trans (prime_reciprocal_le_half p)
  change logarithmicEulerFactorRemainder u (z p) = _
  exact (hasSum_logarithmicEulerFactorRemainder hu0 hu1
    (by linarith : ‖z p‖ < 1)).tsum_eq.symm

/-- Joint absolute convergence of the double Taylor series, with the uniform total bound.
The index `n` stands for the Taylor degree `n+2`. -/
lemma logarithmicEulerDoubleSeries_abs_summable_and_tsum_le {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (z : Nat.Primes → ℂ)
    (hz : ∀ p, ‖z p‖ ≤ (p : ℝ)⁻¹) :
    Summable (fun pn : Nat.Primes × ℕ => ‖logarithmicEulerTaylorTerm u (z pn.1) pn.2‖) ∧
      (∑' pn : Nat.Primes × ℕ, ‖logarithmicEulerTaylorTerm u (z pn.1) pn.2‖) ≤ 1 - u := by
  have hconst : 0 ≤ 1 - u := by linarith
  have hinner (p : Nat.Primes) :
      Summable (fun n => ‖logarithmicEulerTaylorTerm u (z p) n‖) := by
    have hhalf := (hz p).trans (prime_reciprocal_le_half p)
    exact (hasSum_logarithmicEulerFactorRemainder hu0 hu1
      (by linarith : ‖z p‖ < 1)).summable.norm
  have hfinite (S : Finset Nat.Primes) :
      (∑ p ∈ S, ∑' n, ‖logarithmicEulerTaylorTerm u (z p) n‖) ≤ 1 - u := by
    calc
      _ ≤ ∑ p ∈ S, (1 - u) * (‖z p‖ ^ 2 / (1 - ‖z p‖)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hhalf := (hz p).trans (prime_reciprocal_le_half p)
        exact logarithmicEulerTaylorTerm_norm_tsum_le hu0 hu1 (by linarith : ‖z p‖ < 1)
      _ = (1 - u) * ∑ p ∈ S, ‖z p‖ ^ 2 / (1 - ‖z p‖) := by rw [Finset.mul_sum]
      _ ≤ (1 - u) * 1 := mul_le_mul_of_nonneg_left
        (prime_quadratic_majorant_sum_le_one S z (fun p _ => hz p)) hconst
      _ = 1 - u := mul_one _
  have houter : Summable (fun p => ∑' n, ‖logarithmicEulerTaylorTerm u (z p) n‖) :=
    summable_of_sum_le (fun _ => tsum_nonneg (fun _ => norm_nonneg _)) hfinite
  have hprod : Summable (fun pn : Nat.Primes × ℕ =>
      ‖logarithmicEulerTaylorTerm u (z pn.1) pn.2‖) :=
    (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr ⟨hinner, houter⟩
  refine ⟨hprod, ?_⟩
  rw [hprod.tsum_prod]
  exact houter.tsum_le_of_sum_le hfinite

/-- The complex double series is summable, not merely its iterated presentation. -/
lemma logarithmicEulerDoubleSeries_summable {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (z : Nat.Primes → ℂ) (hz : ∀ p, ‖z p‖ ≤ (p : ℝ)⁻¹) :
    Summable (fun pn : Nat.Primes × ℕ => logarithmicEulerTaylorTerm u (z pn.1) pn.2) :=
  (logarithmicEulerDoubleSeries_abs_summable_and_tsum_le hu0 hu1 z hz).1.of_norm

/-- The joint and iterated double sums both equal the logarithmic correction. -/
lemma logarithmicEulerDoubleSeries_tsum_eq {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (z : Nat.Primes → ℂ) (hz : ∀ p, ‖z p‖ ≤ (p : ℝ)⁻¹) :
    (∑' pn : Nat.Primes × ℕ, logarithmicEulerTaylorTerm u (z pn.1) pn.2) =
      logarithmicEulerRemainder z u := by
  rw [(logarithmicEulerDoubleSeries_summable hu0 hu1 z hz).tsum_prod]
  exact (logarithmicEulerRemainder_eq_tsum_tsum hu0 hu1 z hz).symm

end Erdos143
