import Erdos143.ImproperControl

open MeasureTheory

namespace Erdos143

/-- A nonnegative family with an integrable pointwise sum has a summable sequence of
integrals. This supplies the Tonelli finiteness needed before exchanging infinite sums. -/
lemma summable_integral_of_integrable_tsum_nonneg {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (F : ℕ → α → ℝ) (hF : ∀ n, Integrable (F n) μ)
    (hnonneg : ∀ n x, 0 ≤ F n x) (hsum : ∀ᵐ x ∂μ, Summable (fun n => F n x))
    (hInt : Integrable (fun x => ∑' n, F n x) μ) : Summable (fun n => ∫ x, F n x ∂μ) := by
  apply summable_of_sum_le (fun n => integral_nonneg (hnonneg n))
  intro S
  rw [← integral_finset_sum S (fun n _ => hF n)]
  apply integral_mono_ae (integrable_finset_sum S (fun n _ => hF n)) hInt
  filter_upwards [hsum] with x hx
  exact hx.sum_le_tsum S (fun n _ => hnonneg n x)

lemma integral_tsum_nonneg_of_integrable_tsum {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (F : ℕ → α → ℝ) (hF : ∀ n, Integrable (F n) μ)
    (hnonneg : ∀ n x, 0 ≤ F n x) (hsum : ∀ᵐ x ∂μ, Summable (fun n => F n x))
    (hInt : Integrable (fun x => ∑' n, F n x) μ) :
    (∑' n, ∫ x, F n x ∂μ) = ∫ x, ∑' n, F n x ∂μ := by
  have hint := summable_integral_of_integrable_tsum_nonneg F hF hnonneg hsum hInt
  have hnorm : Summable (fun n => ∫ x, ‖F n x‖ ∂μ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg _ _)] using hint
  exact integral_tsum_of_summable_integral_norm hF hnorm

end Erdos143
