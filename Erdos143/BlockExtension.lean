import Erdos143.BlockParameters
import Erdos143.Insertion

noncomputable section
open scoped BigOperators ENNReal
namespace Erdos143

def extendState (F : ConstructionState) (H G D : ℕ) (P : Finset ℕ) : ConstructionState :=
  ⟨F.atoms ∪ P.image (blockAtom H G D), insert H F.primes⟩

lemma extendState_points (F : ConstructionState) (H G D : ℕ) (P : Finset ℕ) :
    (extendState F H G D P).points = F.points ∪ P.image (fun n : ℕ => blockScale H G * D * n) := by
  simp only [extendState, ConstructionState.points, Finset.image_union,
    Finset.image_image, Function.comp_def, blockAtom_value]

lemma block_extension_valid (F : ConstructionState) (hF : ValidState F)
    (H G D U : ℕ) (P : Finset ℕ)
    (hH : H.Prime) (hH2 : 2 < H) (hG : G.Prime) (hD : 1 ≤ D)
    (hGlarge : ∀ h ∈ insert H F.primes, h < G)
    (hnew : ∀ a ∈ F.atoms, a.N < H)
    (hbudget : (∑ h ∈ insert H F.primes, (1 : ℚ) / h) < 1 / 100)
    (havoidD : ∀ h ∈ insert H F.primes, ¬ h ∣ D)
    (hP : Primitive (P : Set ℕ))
    (hn : ∀ n ∈ P, 2 * D ≤ n ∧ 4 * H < D * n ∧ D * n ≤ U ∧
      ∀ h ∈ insert H F.primes, ¬ h ∣ n)
    (hfree : ∀ n ∈ P, RightFree (F.points : Set ℚ) D n)
    (habove : ∀ a ∈ F.points, ∀ n ∈ P, a + 1 < (D * n : ℕ))
    (hq : 2 * U ^ 13 ≤ H * G - 1)
    (hsmall : ∀ a ∈ F.points, ∀ n ∈ P, (D * n : ℚ) / (H * G - 1 : ℕ) < 1 / a.den) :
    ValidState (extendState F H G D P) := by
  have hp : 2 < H * G := by nlinarith [hG.two_le]
  obtain ⟨hc, hc2⟩ := blockScale_bounds hp
  have hqpos : (0 : ℚ) < (H * G - 1 : ℕ) := Nat.cast_pos.mpr (by omega)
  have hn2 (n : ℕ) (hnP : n ∈ P) : 2 ≤ D * n := by
    have := (hn n hnP).1
    nlinarith
  have hshift (n : ℕ) (hnP : n ∈ P) :
      0 < (blockScale H G - 1) * D * n := by
    rw [block_shift_eq (by omega)]
    exact div_pos (Nat.cast_pos.mpr (by have := hn2 n hnP; omega)) hqpos
  have hvalabove (n : ℕ) (hnP : n ∈ P) : (D * n : ℕ) < blockScale H G * D * n := by
    have := hshift n hnP
    push_cast
    nlinarith
  have hprime (h : ℕ) (hh : h ∈ insert H F.primes) : h.Prime ∧ 2 < h := by
    rcases Finset.mem_insert.mp hh with rfl | hh
    · exact ⟨hH, hH2⟩
    · exact hF.prime h hh
  constructor
  · exact hprime
  · exact hbudget
  · intro a ha
    change a ∈ F.atoms ∪ P.image (blockAtom H G D) at ha
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨haH, hN, haq, hav, hsize⟩ := hF.data a ha
      exact ⟨Finset.mem_insert_of_mem haH, hN, haq, hav, hsize⟩
    · obtain ⟨n, hnP, rfl⟩ := Finset.mem_image.mp ha
      refine ⟨by simp [blockAtom, extendState], ?_, ?_, ?_, ?_⟩
      · change 0 < G * D * n
        have : 0 < n := by have := (hn n hnP).1; omega
        exact Nat.mul_pos (Nat.mul_pos hG.pos (by omega)) this
      · change 0 < H * G - 1
        omega
      · exact block_private_denominator hH hG.pos
      · exact block_private_spacing (by omega) hH.pos (hn n hnP).2.1
  · intro h hh a ha
    change h ∈ insert H F.primes at hh
    change a ∈ F.atoms ∪ P.image (blockAtom H G D) at ha
    rcases Finset.mem_union.mp ha with haold | hanew
    · rcases Finset.mem_insert.mp hh with heq | hhold
      · subst h
        exact fresh_prime_avoids_old_part (hF.data a haold).2.1 (hnew a haold)
      · exact hF.avoid h hhold a haold
    · obtain ⟨n, hnP, rfl⟩ := Finset.mem_image.mp hanew
      apply private_prime_preserved (hprime h hh).1 ?_ (havoidD h hh) ((hn n hnP).2.2.2 h hh)
      intro hd
      have heq : h = G := (Nat.dvd_prime hG).mp hd |>.resolve_left (by have := (hprime h hh).2; omega)
      exact (ne_of_lt (hGlarge h hh)) heq
  · intro a ha
    rw [extendState_points] at ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hF.lower a ha
    · obtain ⟨n, hnP, rfl⟩ := Finset.mem_image.mp ha
      have h2 : (2 : ℚ) ≤ (D * n : ℕ) := by exact_mod_cast hn2 n hnP
      exact h2.trans (hvalabove n hnP).le
  · rw [extendState_points, Finset.coe_union, Finset.coe_image]
    apply insert_primitive_block_original hF.original hP hD hc hfree hshift
    · intro a ha n hnP
      rw [block_shift_eq (by omega)]
      simpa only [Nat.cast_mul] using hsmall a ha n hnP
    · intro a ha n hnP
      exact (habove a ha n hnP).trans (hvalabove n hnP)
    · intro n hnP
      exact (Nat.cast_nonneg (D * n)).trans (hvalabove n hnP).le
  · intro a ha
    rw [extendState_points] at ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hF.tiny a ha
    · obtain ⟨n, hnP, rfl⟩ := Finset.mem_image.mp ha
      rw [← blockAtom_value, block_value_eq_perturbed (by omega)]
      exact perturbed_point_tiny (hn2 n hnP) (hn n hnP).2.2.1 hq

lemma state_mass_ne_top (F : ConstructionState) : F.mass ≠ ⊤ := by
  apply ENNReal.sum_ne_top.mpr
  intro a ha
  exact ENNReal.ofReal_ne_top

lemma extendState_mass_gain (F : ConstructionState) (H G D : ℕ) (P : Finset ℕ)
    (hp : 2 < H * G) (hD : 1 ≤ D) (hn : ∀ n ∈ P, 2 * D ≤ n)
    (habove : ∀ a ∈ F.points, ∀ n ∈ P, a + 1 < (D * n : ℕ))
    (hw : (1 / 6 : ℝ≥0∞) < ∑ n ∈ P, weight n) :
    F.mass + (1 : ℝ≥0∞) / (24 * D) < (extendState F H G D P).mass := by
  obtain ⟨hc, hc2⟩ := blockScale_bounds hp
  have hdisj : Disjoint F.points (P.image (fun n : ℕ => blockScale H G * D * n)) := by
    apply Finset.disjoint_left.mpr
    intro a ha hnew
    obtain ⟨n, hnP, rfl⟩ := Finset.mem_image.mp hnew
    have hab := habove _ ha n hnP
    have hDq : (0 : ℚ) ≤ D := Nat.cast_nonneg D
    have hnq : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    push_cast at hab
    nlinarith [mul_nonneg hDq hnq]
  unfold ConstructionState.mass
  rw [extendState_points, Finset.sum_union hdisj]
  apply ENNReal.add_lt_add_left (state_mass_ne_top F)
  simpa only [totalWeight_finset] using block_weight_lower_bound P hc hc2 hD hn hw

end Erdos143
