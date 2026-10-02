import Erdos143.Definitions
import Mathlib.Analysis.Complex.Norm

open scoped BigOperators NNReal

namespace Erdos143

/-- A telescoping product controls all quadratic Euler remainders, even over all integers. -/
lemma correction_product_range (N : ℕ) :
    (∏ n ∈ Finset.range N, (1 - (((n : ℝ) + 2) ^ 2)⁻¹)⁻¹) =
      2 * ((N : ℝ) + 1) / ((N : ℝ) + 2) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.prod_range_succ, ih]
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
    have h3 : (N : ℝ) + 3 ≠ 0 := by positivity
    have hfac : (1 - (((N : ℝ) + 2) ^ 2)⁻¹)⁻¹ =
        ((N : ℝ) + 2) ^ 2 / (((N : ℝ) + 1) * ((N : ℝ) + 3)) := by
      apply inv_injective
      rw [inv_inv, inv_div]
      field_simp
      ring
    rw [hfac]
    push_cast
    field_simp
    ring

lemma correction_factor_one_le (n : ℕ) : (1 : ℝ) ≤ (1 - (((n : ℝ) + 2) ^ 2)⁻¹)⁻¹ := by
  have hpow : (1 : ℝ) < ((n : ℝ) + 2) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hi : (((n : ℝ) + 2) ^ 2)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).2 hpow
  apply (one_le_inv₀ (by linarith : (0 : ℝ) < 1 - (((n : ℝ) + 2) ^ 2)⁻¹)).2
  have : 0 ≤ (((n : ℝ) + 2) ^ 2)⁻¹ := by positivity
  linarith

lemma correction_product_finset_le_two (S : Finset ℕ) :
    (∏ n ∈ S, (1 - (((n : ℝ) + 2) ^ 2)⁻¹)⁻¹) ≤ 2 := by
  let N := S.sup id + 1
  have hsub : S ⊆ Finset.range N := by
    intro n hn
    have hle : n ≤ S.sup id := Finset.le_sup (f := id) hn
    simp only [Finset.mem_range]
    omega
  calc
    _ ≤ ∏ n ∈ Finset.range N, (1 - (((n : ℝ) + 2) ^ 2)⁻¹)⁻¹ := by
      let f : ℕ → ℝ≥0 := fun n => ⟨(1 - (((n : ℝ) + 2) ^ 2)⁻¹)⁻¹,
        (by linarith [correction_factor_one_le n])⟩
      have hle : (∏ n ∈ S, f n) ≤ ∏ n ∈ Finset.range N, f n :=
        Finset.prod_le_prod_of_subset_of_one_le' hsub
          (fun n _ _ => correction_factor_one_le n)
      simpa only [NNReal.coe_prod, f] using (NNReal.coe_le_coe.mpr hle)
    _ = 2 * ((N : ℝ) + 1) / ((N : ℝ) + 2) := correction_product_range N
    _ ≤ 2 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < N + 2)).2
      linarith

lemma prime_reciprocal_le_half (p : Nat.Primes) : (p : ℝ)⁻¹ ≤ 1 / 2 := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp

lemma correction_factor_mono {r R : ℝ} (hr0 : 0 ≤ r) (hrR : r ≤ R) (hR : R ≤ 1 / 2) :
    (1 - r ^ 2)⁻¹ ≤ (1 - R ^ 2)⁻¹ := by
  have hR0 : 0 ≤ R := hr0.trans hrR
  have hpos : 0 < 1 - R ^ 2 := by nlinarith
  have hsquare : r ^ 2 ≤ R ^ 2 := by nlinarith
  simpa only [one_div] using one_div_le_one_div_of_le hpos (sub_le_sub_left hsquare 1)

/-- No prime-distribution theorem is needed for the uniform quadratic correction. -/
lemma prime_correction_product_le_two (S : Finset Nat.Primes) (z : Nat.Primes → ℂ)
    (hz : ∀ p ∈ S, ‖z p‖ ≤ (p : ℝ)⁻¹) :
    (∏ p ∈ S, (1 - ‖z p‖ ^ 2)⁻¹) ≤ 2 := by
  classical
  let e : Nat.Primes → ℕ := fun p => (p : ℕ) - 2
  have heinj : Function.Injective e := by
    intro p q hpq
    apply Subtype.ext
    have hp := p.property.two_le
    have hq := q.property.two_le
    change (p : ℕ) - 2 = (q : ℕ) - 2 at hpq
    omega
  have hecast (p : Nat.Primes) : ((e p : ℕ) : ℝ) + 2 = (p : ℝ) := by
    have h : e p + 2 = (p : ℕ) := Nat.sub_add_cancel p.property.two_le
    exact_mod_cast h
  calc
    _ ≤ ∏ p ∈ S, (1 - ((((e p : ℕ) : ℝ) + 2) ^ 2)⁻¹)⁻¹ := by
      apply Finset.prod_le_prod
      · intro p hp
        have hnorm : ‖z p‖ ≤ 1 / 2 := (hz p hp).trans (prime_reciprocal_le_half p)
        have : 0 < 1 - ‖z p‖ ^ 2 := by nlinarith [norm_nonneg (z p)]
        positivity
      · intro p hp
        rw [hecast]
        simpa only [inv_pow] using correction_factor_mono (norm_nonneg _) (hz p hp)
          (prime_reciprocal_le_half p)
    _ = ∏ n ∈ S.image e, (1 - (((n : ℝ) + 2) ^ 2)⁻¹)⁻¹ := by
      rw [Finset.prod_image]
      intro p hp q hq hpq
      exact heinj hpq
    _ ≤ 2 := correction_product_finset_le_two (S.image e)

end Erdos143
