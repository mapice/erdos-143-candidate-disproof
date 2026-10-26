import Erdos143.CorrectionProducts
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section
open scoped BigOperators Topology

namespace Erdos143

/-- The local logarithmic correction in the revised analytic proof. -/
def logarithmicEulerFactorRemainder (u : ℝ) (z : ℂ) : ℂ :=
  -Complex.log (1 - (u : ℂ) * z) + (u : ℂ) * Complex.log (1 - z)

/-- The coefficient estimate used after cancellation of the linear Euler term. -/
lemma omega_coefficient_remainder_bound {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (n : ℕ) : 0 ≤ u - u ^ (n + 2) ∧
      u - u ^ (n + 2) ≤ ((n : ℝ) + 1) * (1 - u) := by
  have hpow (k : ℕ) : 0 ≤ u ^ k ∧ u ^ k ≤ 1 :=
    ⟨pow_nonneg hu0 _, pow_le_one₀ hu0 hu1⟩
  induction n with
  | zero =>
      norm_num
      constructor <;> nlinarith
  | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ]
      push_cast
      constructor
      · nlinarith [ih.1]
      · nlinarith [(hpow (n + 2)).1, (hpow (n + 2)).2, ih.2]

/-- Taylor expansion of the local correction, with the vanishing constant and linear terms removed. -/
lemma hasSum_logarithmicEulerFactorRemainder {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (((u : ℂ) ^ (n + 2) - (u : ℂ)) * z ^ (n + 2)) /
      ((n + 2 : ℕ) : ℂ)) (logarithmicEulerFactorRemainder u z) := by
  have huz : ‖(u : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
    exact (mul_le_of_le_one_left (norm_nonneg z) hu1).trans_lt hz
  have h := (Complex.hasSum_taylorSeries_neg_log huz).sub
    ((Complex.hasSum_taylorSeries_neg_log hz).mul_left (u : ℂ))
  have hfull : HasSum (fun n : ℕ => (((u : ℂ) ^ n - (u : ℂ)) * z ^ n) / (n : ℂ))
      (logarithmicEulerFactorRemainder u z) := by
    convert h using 1
    · ext n
      rw [mul_pow]
      ring
    · simp [logarithmicEulerFactorRemainder]
  have hshift := (hasSum_nat_add_iff' 2).mpr hfull
  simpa [Finset.sum_range_succ, logarithmicEulerFactorRemainder] using hshift

/-- The coefficient bound after division by the Taylor index. -/
lemma logarithmicEulerFactorRemainder_term_bound {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (z : ℂ) (n : ℕ) :
    ‖(((u : ℂ) ^ (n + 2) - (u : ℂ)) * z ^ (n + 2)) /
      ((n + 2 : ℕ) : ℂ)‖ ≤ (1 - u) * ‖z‖ ^ 2 * ‖z‖ ^ n := by
  have hcoef := omega_coefficient_remainder_bound hu0 hu1 n
  have heq : (u : ℂ) ^ (n + 2) - (u : ℂ) = ((u ^ (n + 2) - u : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [norm_div, norm_mul, heq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith : u ^ (n + 2) - u ≤ 0), norm_pow, norm_natCast]
  have hden : (0 : ℝ) < n + 2 := by positivity
  rw [div_le_iff₀ (by exact_mod_cast Nat.zero_lt_succ (n + 1) :
    (0 : ℝ) < (n + 2 : ℕ))]
  push_cast
  have hb : u - u ^ (n + 2) ≤ ((n : ℝ) + 2) * (1 - u) := by
    nlinarith
  calc
    -(u ^ (n + 2) - u) * ‖z‖ ^ (n + 2) = (u - u ^ (n + 2)) * ‖z‖ ^ (n + 2) := by ring
    _ ≤ (((n : ℝ) + 2) * (1 - u)) * ‖z‖ ^ (n + 2) :=
      mul_le_mul_of_nonneg_right hb (pow_nonneg (norm_nonneg z) _)
    _ = _ := by rw [pow_add]; ring

/-- Uniform local logarithmic correction estimate from its absolutely convergent Taylor series. -/
lemma logarithmicEulerFactorRemainder_norm_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖logarithmicEulerFactorRemainder u z‖ ≤ (1 - u) * ‖z‖ ^ 2 / (1 - ‖z‖) := by
  let f : ℕ → ℂ := fun n => (((u : ℂ) ^ (n + 2) - (u : ℂ)) * z ^ (n + 2)) /
    ((n + 2 : ℕ) : ℂ)
  have hf := hasSum_logarithmicEulerFactorRemainder hu0 hu1 hz
  have hg := (hasSum_geometric_of_lt_one (norm_nonneg z) hz).mul_left
    ((1 - u) * ‖z‖ ^ 2)
  rw [← hf.tsum_eq]
  calc
    ‖∑' n, f n‖ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hf.summable.norm
    _ ≤ ∑' n, (1 - u) * ‖z‖ ^ 2 * ‖z‖ ^ n :=
      Summable.tsum_le_tsum (logarithmicEulerFactorRemainder_term_bound hu0 hu1 z)
        hf.summable.norm hg.summable
    _ = (1 - u) * ‖z‖ ^ 2 / (1 - ‖z‖) := by
      rw [hg.tsum_eq]
      rfl

/-- Telescoping majorant for the quadratic Euler tails over all integers at least two. -/
lemma quadratic_tail_sum_range (N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) =
      1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      ring

lemma quadratic_tail_sum_finset_le_one (S : Finset ℕ) :
    (∑ n ∈ S, 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) ≤ 1 := by
  let N := S.sup id + 1
  have hsub : S ⊆ Finset.range N := by
    intro n hn
    have hn' : n ≤ S.sup id := Finset.le_sup (f := id) hn
    simp only [Finset.mem_range]
    omega
  calc
    _ ≤ ∑ n ∈ Finset.range N, 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = 1 - 1 / ((N : ℝ) + 1) := quadratic_tail_sum_range N
    _ ≤ 1 := by
      have h : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
      linarith

lemma quadratic_geometric_majorant_mono {r R : ℝ} (hr0 : 0 ≤ r) (hrR : r ≤ R)
    (hR : R < 1) : r ^ 2 / (1 - r) ≤ R ^ 2 / (1 - R) := by
  have hR0 : 0 ≤ R := hr0.trans hrR
  have hden : 0 < 1 - R := by linarith
  have hrden : 0 < 1 - r := by linarith
  exact div_le_div₀ (sq_nonneg R) (by nlinarith) hden (by linarith)

/-- The sum of the quadratic geometric majorants over any finite set of primes is at most one. -/
lemma prime_quadratic_majorant_sum_le_one (S : Finset Nat.Primes) (z : Nat.Primes → ℂ)
    (hz : ∀ p ∈ S, ‖z p‖ ≤ (p : ℝ)⁻¹) :
    (∑ p ∈ S, ‖z p‖ ^ 2 / (1 - ‖z p‖)) ≤ 1 := by
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
    _ ≤ ∑ p ∈ S, 1 / ((((e p : ℕ) : ℝ) + 1) * (((e p : ℕ) : ℝ) + 2)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hhalf := prime_reciprocal_le_half p
      have hmono := quadratic_geometric_majorant_mono (norm_nonneg (z p)) (hz p hp)
        (by linarith : (p : ℝ)⁻¹ < 1)
      apply hmono.trans_eq
      rw [← hecast]
      have h1 : ((e p : ℕ) : ℝ) + 1 ≠ 0 := by positivity
      have h2 : ((e p : ℕ) : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      ring_nf
      field_simp
      ring
    _ = ∑ n ∈ S.image e, 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
      rw [Finset.sum_image]
      intro p hp q hq hpq
      exact heinj hpq
    _ ≤ 1 := quadratic_tail_sum_finset_le_one (S.image e)

/-- Uniform remainder bound over any finite collection of prime Euler factors. -/
lemma prime_logarithmic_remainder_sum_norm_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (S : Finset Nat.Primes) (z : Nat.Primes → ℂ)
    (hz : ∀ p ∈ S, ‖z p‖ ≤ (p : ℝ)⁻¹) :
    (∑ p ∈ S, ‖logarithmicEulerFactorRemainder u (z p)‖) ≤ 1 - u := by
  have hconst : 0 ≤ 1 - u := by linarith
  calc
    _ ≤ ∑ p ∈ S, (1 - u) * (‖z p‖ ^ 2 / (1 - ‖z p‖)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hhalf := (hz p hp).trans (prime_reciprocal_le_half p)
      simpa [div_eq_mul_inv, mul_assoc] using
        logarithmicEulerFactorRemainder_norm_le hu0 hu1 (by linarith : ‖z p‖ < 1)
    _ = (1 - u) * ∑ p ∈ S, ‖z p‖ ^ 2 / (1 - ‖z p‖) := by rw [Finset.mul_sum]
    _ ≤ (1 - u) * 1 := mul_le_mul_of_nonneg_left
      (prime_quadratic_majorant_sum_le_one S z hz) hconst
    _ = 1 - u := mul_one _

/-- Absolute summability and the uniform bound for the full logarithmic remainder. -/
lemma prime_logarithmic_remainder_summable_and_norm_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (z : Nat.Primes → ℂ) (hz : ∀ p, ‖z p‖ ≤ (p : ℝ)⁻¹) :
    Summable (fun p => logarithmicEulerFactorRemainder u (z p)) ∧
      ‖∑' p, logarithmicEulerFactorRemainder u (z p)‖ ≤ 1 - u := by
  have hfinite (S : Finset Nat.Primes) :
      (∑ p ∈ S, ‖logarithmicEulerFactorRemainder u (z p)‖) ≤ 1 - u :=
    prime_logarithmic_remainder_sum_norm_le hu0 hu1 S z (fun p _ => hz p)
  have hsum : Summable (fun p => ‖logarithmicEulerFactorRemainder u (z p)‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _) hfinite
  refine ⟨hsum.of_norm, (norm_tsum_le_tsum_norm hsum).trans ?_⟩
  exact hsum.tsum_le_of_sum_le hfinite

end Erdos143
