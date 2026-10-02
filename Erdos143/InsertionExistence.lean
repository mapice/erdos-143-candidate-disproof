import Erdos143.BlockExtension

noncomputable section
open scoped BigOperators ENNReal
namespace Erdos143

lemma labels_threshold (F : Finset ℚ) (H D : ℕ) (hD : 1 ≤ D) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      2 * D ≤ n ∧ 4 * H < D * n ∧ ∀ a ∈ F, a + 1 < (D * n : ℕ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((∑ a ∈ F, |a|) + 2 * D + 4 * H + 3 : ℚ)
  have hsum : (0 : ℚ) ≤ ∑ a ∈ F, |a| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hN2 : 2 ≤ N := by
    have : (2 : ℚ) < N := by linarith [(show (0 : ℚ) ≤ D from Nat.cast_nonneg D), (show (0 : ℚ) ≤ H from Nat.cast_nonneg H)]
    exact_mod_cast this.le
  refine ⟨N, hN2, ?_⟩
  intro n hn
  have hn' : (N : ℚ) ≤ n := by exact_mod_cast hn
  have hmul : n ≤ D * n := by nlinarith
  have hmul' : (n : ℚ) ≤ (D * n : ℕ) := by exact_mod_cast hmul
  refine ⟨?_, ?_, ?_⟩
  · have : (2 : ℚ) * D ≤ n := by linarith
    exact_mod_cast this
  · have : (4 : ℚ) * H < (D * n : ℕ) := by linarith
    exact_mod_cast this
  · intro a ha
    have hs : |a| ≤ ∑ b ∈ F, |b| := Finset.single_le_sum (fun b _ => abs_nonneg b) ha
    linarith [le_abs_self a]

/-- One complete block insertion. Old-round points use the reset grid; current-round
points use their virtual roots. Every required parameter is constructed here. -/
lemma insert_block_exists (base F : ConstructionState) (hb : ValidState base) (hF : ValidState F)
    (D : ℕ) (hD : 48 ≤ D) (R : Finset ℕ)
    (hdiv : ∀ a ∈ base.atoms, a.N ∣ D)
    (hbaseprimes : base.primes ⊆ F.primes)
    (havoidD : ∀ h ∈ F.primes, ¬ h ∣ D)
    (hroots : ∀ p ∈ R, 2 * D ≤ p)
    (hcard : R.card ≤ D / 12)
    (hcover : ∀ a ∈ F.points, a ∈ base.points ∨
      ∃ p ∈ R, ∃ m : ℕ, a = ((p : ℚ) / (p - 1 : ℕ)) * D * m) :
    ∃ (F' : ConstructionState) (p : ℕ), ValidState F' ∧
      F.atoms ⊆ F'.atoms ∧ F.primes ⊆ F'.primes ∧
      (∀ h ∈ F'.primes, ¬ h ∣ D) ∧ 2 * D ≤ p ∧
      (∀ a ∈ F'.points, a ∈ base.points ∨
        ∃ r ∈ insert p R, ∃ m : ℕ, a = ((r : ℚ) / (r - 1 : ℕ)) * D * m) ∧
      F.mass + (1 : ℝ≥0∞) / (24 * D) < F'.mass := by
  classical
  obtain ⟨H, hH, hHD, hH2, _, hnew, hbudget⟩ := fresh_private_prime F hF D
  have hD1 : 1 ≤ D := by omega
  have hD0 : 0 < D := by omega
  have havD (h : ℕ) (hh : h ∈ insert H F.primes) : ¬ h ∣ D := by
    rcases Finset.mem_insert.mp hh with rfl | hh
    · exact Nat.not_dvd_of_pos_of_lt hD0 hHD
    · exact havoidD h hh
  obtain ⟨N, hN, hthreshold⟩ := labels_threshold F.points H D hD1
  obtain ⟨P, hP, hprim, hw⟩ := round_labels (insert H F.primes) R D N
    (by
      intro h hh
      rcases Finset.mem_insert.mp hh with rfl | hh
      · exact hH.pos
      · exact (hF.prime h hh).1.pos)
    hD0 (by intro p hp; have := hroots p hp; omega) hbudget hcard hN
  let U := D * P.sup id
  let B := F.points.sup Rat.den
  let Q := 2 * U ^ 13 + U * B + 2 * D + 2
  obtain ⟨G, hG, hGlarge, hQ⟩ := auxiliary_prime_exists H Q (by omega) (insert H F.primes)
  have hp : 2 < H * G := by nlinarith [hG.two_le]
  have hq : 2 * U ^ 13 ≤ H * G - 1 := by dsimp [Q] at hQ; omega
  have hpD : 2 * D ≤ H * G := by dsimp [Q] at hQ; omega
  have hn (n : ℕ) (hnP : n ∈ P) :
      2 * D ≤ n ∧ 4 * H < D * n ∧ D * n ≤ U ∧
        ∀ h ∈ insert H F.primes, ¬ h ∣ n := by
    obtain ⟨hn2, hn4, _⟩ := hthreshold n (hP n hnP).1
    exact ⟨hn2, hn4, Nat.mul_le_mul_left D (Finset.le_sup (f := id) hnP), (hP n hnP).2.1⟩
  have habove (a : ℚ) (ha : a ∈ F.points) (n : ℕ) (hnP : n ∈ P) : a + 1 < (D * n : ℕ) :=
    (hthreshold n (hP n hnP).1).2.2 a ha
  have hfree (n : ℕ) (hnP : n ∈ P) : RightFree (F.points : Set ℚ) D n := by
    intro a ha k hcoll
    rcases hcover a ha with haold | ⟨p, hpR, m, rfl⟩
    · exact state_grid_free base hb hdiv
        (fun h hh => havoidD h (hbaseprimes hh))
        (fun h hh => (hP n hnP).2.1 h (Finset.mem_insert_of_mem (hbaseprimes hh))) a haold k hcoll
    · have hp2 : 1 < p := by have := hroots p hpR; omega
      have hsep := root_not_bad_separated hp2 hD0 ((hP n hnP).2.2 p hpR) (k * m)
      have heq : (k : ℚ) * ((p : ℚ) / (p - 1 : ℕ) * D * m) - D * n =
          (p : ℚ) / (p - 1 : ℕ) * D * (k * m : ℤ) - D * n := by push_cast; ring
      rw [← heq] at hsep
      have hle := abs_le.mpr ⟨hcoll.1.le, hcoll.2⟩
      linarith
  have hsmall (a : ℚ) (ha : a ∈ F.points) (n : ℕ) (hnP : n ∈ P) :
      (D * n : ℚ) / (H * G - 1 : ℕ) < 1 / a.den := by
    have hden : a.den ≤ B := Finset.le_sup (f := Rat.den) ha
    have hmn := (hn n hnP).2.2.1
    have hprod : D * n * a.den < H * G - 1 := by
      have : D * n * a.den ≤ U * B := Nat.mul_le_mul hmn hden
      dsimp [Q] at hQ
      omega
    have hqpos : (0 : ℚ) < (H * G - 1 : ℕ) := Nat.cast_pos.mpr (by omega)
    have hdenpos : (0 : ℚ) < a.den := Nat.cast_pos.mpr a.den_pos
    apply (div_lt_div_iff₀ hqpos hdenpos).mpr
    simpa only [one_mul, Nat.cast_mul] using (Nat.cast_lt (α := ℚ)).mpr hprod
  let F' := extendState F H G D P
  refine ⟨F', H * G, block_extension_valid F hF H G D U P hH hH2 hG hD1 hGlarge
    hnew hbudget havD hprim hn hfree habove hq hsmall, ?_, ?_, ?_, hpD, ?_, ?_⟩
  · exact Finset.subset_union_left
  · exact Finset.subset_insert _ _
  · exact havD
  · intro a ha
    rw [extendState_points] at ha
    rcases Finset.mem_union.mp ha with ha | ha
    · rcases hcover a ha with h | ⟨r, hr, m, hm⟩
      · exact Or.inl h
      · exact Or.inr ⟨r, Finset.mem_insert_of_mem hr, m, hm⟩
    · obtain ⟨n, hnP, rfl⟩ := Finset.mem_image.mp ha
      exact Or.inr ⟨H * G, Finset.mem_insert_self _ _, n, rfl⟩
  · exact extendState_mass_gain F H G D P hp hD1 (fun n hnP => (hn n hnP).1) habove hw

end Erdos143
