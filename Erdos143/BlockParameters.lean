import Erdos143.ConstructionState

noncomputable section
namespace Erdos143

def blockAtom (H G D n : ℕ) : StoredPoint := ⟨H, G * D * n, H * G - 1⟩
def blockScale (H G : ℕ) : ℚ := (H * G : ℕ) / (H * G - 1 : ℕ)

lemma blockAtom_value (H G D n : ℕ) :
    (blockAtom H G D n).value = blockScale H G * D * n := by
  simp only [blockAtom, StoredPoint.value, blockScale, Nat.cast_mul]
  ring

lemma blockScale_eq {H G : ℕ} (hp : 1 < H * G) :
    blockScale H G = 1 + 1 / (H * G - 1 : ℕ) := by
  have hq : (H * G - 1 : ℕ) ≠ 0 := by omega
  have heq : H * G = (H * G - 1) + 1 := by omega
  unfold blockScale
  conv_lhs => rw [heq]
  push_cast
  field_simp

lemma blockScale_bounds {H G : ℕ} (hp : 2 < H * G) :
    1 < blockScale H G ∧ blockScale H G < 2 := by
  rw [blockScale_eq (by omega)]
  have hq : (1 : ℚ) < (H * G - 1 : ℕ) := by exact_mod_cast (by omega : 1 < H * G - 1)
  constructor
  · have : (0 : ℚ) < 1 / (H * G - 1 : ℕ) := by positivity
    linarith
  · have : (1 : ℚ) / (H * G - 1 : ℕ) < 1 := (div_lt_one (by linarith)).mpr hq
    linarith

lemma block_shift_eq {H G D n : ℕ} (hp : 1 < H * G) :
    (blockScale H G - 1) * D * n = (D * n : ℕ) / (H * G - 1 : ℕ) := by
  rw [blockScale_eq hp]
  push_cast
  ring

lemma block_value_eq_perturbed {H G D n : ℕ} (hp : 1 < H * G) :
    (blockAtom H G D n).value = (D * n : ℕ) + (D * n : ℕ) / (H * G - 1 : ℕ) := by
  rw [blockAtom_value, blockScale_eq hp]
  push_cast
  ring

/-- The auxiliary prime is selected only after the finite label set, so its
size can dominate every perturbation and old-denominator requirement. -/
lemma auxiliary_prime_exists (H Q : ℕ) (hs : 1 < H) (S : Finset ℕ) :
    ∃ G : ℕ, G.Prime ∧ (∀ h ∈ S, h < G) ∧ Q < H * G - 1 := by
  obtain ⟨G, hG, hlarge⟩ := exists_prime_above_finset (insert (Q + 2) S)
  refine ⟨G, hG, fun h hh => hlarge h (by simp [hh]), ?_⟩
  have hq := hlarge (Q + 2) (by simp)
  have : G ≤ H * G := by nlinarith [hG.pos]
  omega

lemma block_private_denominator {H G : ℕ} (hH : H.Prime) (hG : 0 < G) :
    ¬ H ∣ H * G - 1 := by
  have hp : 0 < H * G := Nat.mul_pos hH.pos hG
  intro hd
  have hone : H ∣ 1 := by
    have hs : H * G - 1 + 1 = H * G := by omega
    have hm : H ∣ H * G - 1 + 1 := by rw [hs]; exact dvd_mul_right H G
    exact (Nat.dvd_add_right hd).mp hm
  exact hH.not_dvd_one hone

lemma block_private_spacing {H G D n : ℕ} (hp : 1 < H * G) (hH : 0 < H)
    (hn : 4 * H < D * n) : 4 < (blockAtom H G D n).value / H := by
  have hH' : (0 : ℚ) < H := Nat.cast_pos.mpr hH
  have hn' : (4 : ℚ) * H < (D * n : ℕ) := by exact_mod_cast hn
  have hq : (0 : ℚ) < (H * G - 1 : ℕ) := Nat.cast_pos.mpr (by omega)
  rw [block_value_eq_perturbed hp]
  apply (lt_div_iff₀ hH').mpr
  have hpos : (0 : ℚ) < (D * n : ℕ) / (H * G - 1 : ℕ) := div_pos (by linarith) hq
  linarith

end Erdos143
