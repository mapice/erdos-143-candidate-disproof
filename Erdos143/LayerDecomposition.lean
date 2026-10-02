import Erdos143.LogWeights
import Erdos143.Levels

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped ArithmeticFunction.Omega

namespace Erdos143

lemma two_pow_length_le_prod (l : List ℕ) (hl : ∀ p ∈ l, 2 ≤ p) : 2 ^ l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp : 2 ≤ p := hl p (by simp)
    have ht : ∀ q ∈ l, 2 ≤ q := fun q hq => hl q (by simp [hq])
    simp only [List.length_cons, List.prod_cons, pow_succ]
    exact (Nat.mul_le_mul_right 2 (ih ht)).trans
      (by simpa [Nat.mul_comm] using Nat.mul_le_mul_right l.prod hp)

lemma two_pow_omega_le {n : ℕ} (hn : n ≠ 0) : 2 ^ Ω n ≤ n := by
  rw [ArithmeticFunction.cardFactors_apply]
  calc
    _ ≤ n.primeFactorsList.prod := two_pow_length_le_prod _ (fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le)
    _ = n := Nat.prod_primeFactorsList hn

def setAbelMass (E : Set ℕ) (u : ℝ) : ℝ := ∑' n, E.indicator (realAbelTerm u) n

def layerMass (E : Set ℕ) (r : ℕ) : ℝ := ∑' n : {n : ℕ | Ω n = r}, E.indicator natWeight n

lemma layerMass_nonneg (E : Set ℕ) (r : ℕ) : 0 ≤ layerMass E r := by
  apply tsum_nonneg
  intro n
  exact Set.indicator_nonneg (fun _ _ => natWeight_nonneg _) _

lemma layerMass_eq_tsum_conditional (E : Set ℕ) (r : ℕ) :
    layerMass E r = ∑' n : ℕ, if Ω n = r ∧ n ∈ E then natWeight n else 0 := by
  classical
  rw [layerMass, tsum_subtype]
  apply tsum_congr
  intro n
  by_cases hr : Ω n = r <;> by_cases hE : n ∈ E <;>
    simp [hr, hE]

lemma layer_weight_summable (E : Set ℕ) (r : ℕ) :
    Summable (fun n : ℕ => if Ω n = r ∧ n ∈ E then natWeight n else 0) := by
  classical
  have hsum := (realAbelTerm_summable (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_left ((2 : ℝ) ^ r)
  apply hsum.of_nonneg_of_le
  · intro n
    split_ifs
    · exact natWeight_nonneg n
    · exact le_rfl
  · intro n
    by_cases hn : Ω n = r ∧ n ∈ E
    · rw [if_pos hn]
      unfold realAbelTerm
      rw [hn.1]
      have hcancel : (2 : ℝ) ^ r * (1 / 2) ^ r = 1 := by rw [← mul_pow]; norm_num
      rw [← mul_assoc, hcancel, one_mul]
    · rw [if_neg hn]
      exact mul_nonneg (by positivity) (realAbelTerm_nonneg (by norm_num) n)

lemma setAbelTerm_summable (E : Set ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Summable (E.indicator (realAbelTerm u)) := (realAbelTerm_summable hu0 hu1).indicator E

/-- Grouping by Ω is justified by absolute summability, and counts multiplicity exactly. -/
lemma layer_abel_hasSum (E : Set ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    HasSum (fun r : ℕ => u ^ r * layerMass E r) (setAbelMass E u) := by
  classical
  have hsum := (setAbelTerm_summable E hu0 hu1).hasSum.tsum_fiberwise Ω
  have hfiber (r : ℕ) :
      (∑' n : {n : ℕ | Ω n = r}, E.indicator (realAbelTerm u) n) = u ^ r * layerMass E r := by
    calc
      _ = ∑' n : {n : ℕ | Ω n = r}, u ^ r * E.indicator natWeight n := by
        apply tsum_congr
        intro n
        have hn : Ω (n : ℕ) = r := n.property
        by_cases hE : (n : ℕ) ∈ E
        · simp only [Set.indicator_of_mem hE, realAbelTerm, hn]
        · simp only [Set.indicator_of_notMem hE, mul_zero]
      _ = _ := tsum_mul_left
  change HasSum (fun r => ∑' n : {n : ℕ | Ω n = r}, E.indicator (realAbelTerm u) n)
    (setAbelMass E u) at hsum
  simpa only [hfiber] using hsum

lemma nat_le_two_pow (r : ℕ) : r ≤ 2 ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hp : 0 < 2 ^ r := pow_pos (by decide) _
    rw [pow_succ]
    omega

lemma omega_le_self (n : ℕ) : Ω n ≤ n := by
  by_cases hn : n = 0
  · simp [hn]
  · exact (nat_le_two_pow _).trans (two_pow_omega_le hn)

end Erdos143
