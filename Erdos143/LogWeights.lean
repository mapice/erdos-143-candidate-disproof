import Erdos143.TwistedIntegral

noncomputable section
open Complex
open scoped ArithmeticFunction.Omega ENNReal

namespace Erdos143

def natWeight (n : ℕ) : ℝ := 1 / ((n : ℝ) * Real.log n)

@[simp] lemma natWeight_zero : natWeight 0 = 0 := by simp [natWeight]
@[simp] lemma natWeight_one : natWeight 1 = 0 := by simp [natWeight]

lemma natWeight_nonneg (n : ℕ) : 0 ≤ natWeight n := by
  by_cases hn : n = 0
  · simp [hn]
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hlog := Real.log_nonneg hnR
    unfold natWeight
    positivity

lemma natWeight_pos {n : ℕ} (hn : 2 ≤ n) : 0 < natWeight n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_pos (show (1 : ℝ) < n by linarith)
  unfold natWeight
  positivity

lemma weight_nat_eq_ofReal (n : ℕ) : weight n = ENNReal.ofReal (natWeight n) := by
  simp [weight, natWeight]

def realAbelTerm (u : ℝ) (n : ℕ) : ℝ := u ^ Ω n * natWeight n

@[simp] lemma realAbelTerm_zero (u : ℝ) : realAbelTerm u 0 = 0 := by simp [realAbelTerm]
@[simp] lemma realAbelTerm_one (u : ℝ) : realAbelTerm u 1 = 0 := by simp [realAbelTerm]

lemma realAbelTerm_nonneg {u : ℝ} (hu : 0 ≤ u) (n : ℕ) : 0 ≤ realAbelTerm u n :=
  mul_nonneg (pow_nonneg hu _) (natWeight_nonneg n)

lemma realAbelTerm_summable {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) : Summable (realAbelTerm u) := by
  apply (summable_nat_add_iff 2).mp
  simpa only [realAbelTerm, natWeight, Nat.cast_add, Nat.cast_ofNat, mul_one_div] using
    weighted_log_series_summable hu0 hu1

def fullWeightedCharacterTerm {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℝ) (n : ℕ) : ℂ :=
  χ n * (realAbelTerm u n : ℂ)

@[simp] lemma fullWeightedCharacterTerm_zero {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℝ) :
    fullWeightedCharacterTerm χ u 0 = 0 := by simp [fullWeightedCharacterTerm]
@[simp] lemma fullWeightedCharacterTerm_one {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℝ) :
    fullWeightedCharacterTerm χ u 1 = 0 := by simp [fullWeightedCharacterTerm]

lemma fullWeightedCharacterTerm_shift {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℝ) (n : ℕ) :
    fullWeightedCharacterTerm χ u (n + 2) = weightedCharacterTerm χ u n := by
  unfold fullWeightedCharacterTerm weightedCharacterTerm realAbelTerm natWeight
  push_cast
  ring

lemma fullWeightedCharacterTerm_summable {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) : Summable (fullWeightedCharacterTerm χ u) := by
  apply (summable_nat_add_iff 2).mp
  simpa only [fullWeightedCharacterTerm_shift] using weightedCharacterTerm_summable χ hu0 hu1

lemma integratedGeneratingValue_eq_full_series {N : ℕ} (χ : DirichletCharacter ℂ N)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    integratedGeneratingValue χ u = ∑' n, fullWeightedCharacterTerm χ u n := by
  rw [integratedGeneratingValue_eq_weighted_series χ hu0 hu1]
  have h := (fullWeightedCharacterTerm_summable χ hu0 hu1).sum_add_tsum_nat_add 2
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, fullWeightedCharacterTerm_zero,
    fullWeightedCharacterTerm_one, zero_add, fullWeightedCharacterTerm_shift] using h

end Erdos143
