import Erdos143.LogWeights
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

noncomputable section
open Complex DirichletCharacter
open scoped BigOperators

namespace Erdos143

def progressionTerm (N : ℕ) (b : ZMod N) (u : ℝ) (n : ℕ) : ℝ :=
  if (n : ZMod N) = b then realAbelTerm u n else 0

def progressionMass (N : ℕ) (b : ZMod N) (u : ℝ) : ℝ := ∑' n, progressionTerm N b u n

lemma progressionTerm_nonneg {N : ℕ} (b : ZMod N) {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    0 ≤ progressionTerm N b u n := by
  unfold progressionTerm
  split_ifs
  · exact realAbelTerm_nonneg hu n
  · exact le_rfl

lemma progressionTerm_summable {N : ℕ} (b : ZMod N) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Summable (progressionTerm N b u) := by
  apply (realAbelTerm_summable hu0 hu1).of_nonneg_of_le (progressionTerm_nonneg b hu0)
  intro n
  unfold progressionTerm
  split_ifs
  · exact le_rfl
  · exact realAbelTerm_nonneg hu0 n

lemma progressionMass_nonneg {N : ℕ} (b : ZMod N) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ progressionMass N b u := tsum_nonneg (progressionTerm_nonneg b hu)

lemma progressionTerm_orthogonality {N : ℕ} [NeZero N] {b : ZMod N} (hb : IsUnit b)
    (u : ℝ) (n : ℕ) :
    (progressionTerm N b u n : ℂ) = (N.totient : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ N, χ b⁻¹ * fullWeightedCharacterTerm χ u n := by
  have hφ : (N.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos N)).ne'
  rw [eq_inv_mul_iff_mul_eq₀ hφ]
  simp only [fullWeightedCharacterTerm, ← mul_assoc, ← Finset.sum_mul,
    sum_char_inv_mul_char_eq ℂ hb (n : ZMod N)]
  by_cases hn : (n : ZMod N) = b
  · simp [progressionTerm, hn]
  · simp [progressionTerm, hn, Ne.symm hn]

/-- Orthogonality after the absolutely justified weighted summation. -/
lemma progressionMass_orthogonality {N : ℕ} [NeZero N] {b : ZMod N} (hb : IsUnit b)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (progressionMass N b u : ℂ) = (N.totient : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ N, χ b⁻¹ * integratedGeneratingValue χ u := by
  unfold progressionMass
  rw [Complex.ofReal_tsum]
  simp_rw [progressionTerm_orthogonality hb]
  rw [tsum_mul_left]
  congr 1
  rw [Summable.tsum_finsetSum (fun χ _ => (fullWeightedCharacterTerm_summable χ hu0 hu1).mul_left _)]
  apply Finset.sum_congr rfl
  intro χ _
  rw [tsum_mul_left, integratedGeneratingValue_eq_full_series χ hu0 hu1]

lemma principal_character_inverse_unit {N : ℕ} {b : ZMod N} (hb : IsUnit b) :
    (1 : DirichletCharacter ℂ N) b⁻¹ = 1 := by
  have h := congrArg (fun x : ZMod N => (1 : DirichletCharacter ℂ N) x) (ZMod.inv_mul_of_unit b hb)
  simpa only [map_mul, map_one, MulChar.one_apply hb, mul_one] using h

lemma progressionMass_natCast_congr {N M b c : ℕ} (hNM : N = M) (hbc : b = c) (u : ℝ) :
    progressionMass N (b : ZMod N) u = progressionMass M (c : ZMod M) u := by
  subst M
  subst c
  rfl

end Erdos143
