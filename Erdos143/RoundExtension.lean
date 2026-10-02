import Erdos143.InsertionExistence

noncomputable section
open scoped BigOperators ENNReal
namespace Erdos143

lemma round_gain_bound {D : ℕ} (hD : 48 ≤ D) :
    (1 : ℝ≥0∞) / 576 ≤ ((D / 12 : ℕ) : ℝ≥0∞) * (1 / (24 * D)) := by
  have hD0 : D ≠ 0 := by omega
  apply (ENNReal.toReal_le_toReal (by norm_num)
    (ENNReal.mul_ne_top (by simp) (ENNReal.div_ne_top (by norm_num) (by simp [hD0])))).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat,
    ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hJ : (D : ℝ) / 24 ≤ ((D / 12 : ℕ) : ℝ) := by
    have hcast := Rat.cast_le (K := ℝ) |>.mpr (round_blocks_lower_bound hD)
    push_cast at hcast
    exact hcast
  have hDpos : (0 : ℝ) < D := Nat.cast_pos.mpr (by omega)
  rw [mul_one_div]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 24 * D)).mpr
  nlinarith

/-- Finite induction inside one round, retaining every invariant and adding one
proved block gain at each step. -/
lemma round_prefix_exists (base : ConstructionState) (hb : ValidState base)
    (D : ℕ) (hD : 48 ≤ D) (hdiv : ∀ a ∈ base.atoms, a.N ∣ D)
    (havoidD : ∀ h ∈ base.primes, ¬ h ∣ D) (s : ℕ) (hs : s ≤ D / 12) :
    ∃ (F : ConstructionState) (R : Finset ℕ), ValidState F ∧
      base.atoms ⊆ F.atoms ∧ base.primes ⊆ F.primes ∧
      (∀ h ∈ F.primes, ¬ h ∣ D) ∧ (∀ p ∈ R, 2 * D ≤ p) ∧ R.card ≤ s ∧
      (∀ a ∈ F.points, a ∈ base.points ∨
        ∃ p ∈ R, ∃ m : ℕ, a = ((p : ℚ) / (p - 1 : ℕ)) * D * m) ∧
      base.mass + (s : ℝ≥0∞) * (1 / (24 * D)) ≤ F.mass := by
  induction s with
  | zero =>
    refine ⟨base, ∅, hb, Finset.Subset.refl _, Finset.Subset.refl _, havoidD,
      by simp, by simp, ?_, ?_⟩
    · intro a ha
      exact Or.inl ha
    · simp
  | succ s ih =>
    obtain ⟨F, R, hF, hba, hbp, hav, hr, hcard, hcover, hmass⟩ := ih (by omega)
    obtain ⟨F', p, hF', hfa, hfp, hav', hpD, hcover', hgain⟩ :=
      insert_block_exists base F hb hF D hD R hdiv hbp hav hr (by omega) hcover
    refine ⟨F', insert p R, hF', hba.trans hfa, hbp.trans hfp, hav', ?_, ?_, hcover', ?_⟩
    · intro r hrR
      rcases Finset.mem_insert.mp hrR with rfl | hrR
      · exact hpD
      · exact hr r hrR
    · exact (Finset.card_insert_le p R).trans (by omega)
    · calc
        base.mass + (s.succ : ℝ≥0∞) * (1 / (24 * D)) =
            (base.mass + (s : ℝ≥0∞) * (1 / (24 * D))) + (1 / (24 * D)) := by
          rw [Nat.cast_succ]
          ring
        _ ≤ F.mass + (1 / (24 * D)) := add_le_add_right hmass _
        _ ≤ F'.mass := hgain.le

/-- An entire round always exists, with a gain bounded uniformly away from zero. -/
lemma round_extension_exists (F : ConstructionState) (hF : ValidState F) :
    ∃ F' : ConstructionState, ValidState F' ∧ F.atoms ⊆ F'.atoms ∧
      F.primes ⊆ F'.primes ∧ F.mass + (1 : ℝ≥0∞) / 576 ≤ F'.mass := by
  obtain ⟨D, hD, hdiv, hav⟩ := state_grid_exists F hF
  obtain ⟨F', _, hF', hfa, hfp, _, _, _, _, hmass⟩ :=
    round_prefix_exists F hF D hD hdiv hav (D / 12) le_rfl
  exact ⟨F', hF', hfa, hfp, (add_le_add_left (round_gain_bound hD) F.mass).trans hmass⟩

end Erdos143
