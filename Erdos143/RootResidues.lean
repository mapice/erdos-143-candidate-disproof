import Erdos143.Definitions
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic

noncomputable section
open scoped BigOperators
namespace Erdos143

/-- A deliberately closed forbidden interval, larger than the candidate's half-open one. -/
def rootBadResidues (p D : ℕ) : Finset (ZMod p) :=
  (Finset.Icc (-((p - 1) / D : ℕ) : ℤ) (((p - 1) / D : ℕ) : ℤ)).image
    (fun z : ℤ => (z : ZMod p))

lemma rootBadResidues_card_le (p D : ℕ) :
    (rootBadResidues p D).card ≤ 2 * ((p - 1) / D) + 1 := by
  unfold rootBadResidues
  calc
    _ ≤ _ := Finset.card_image_le
    _ = _ := by rw [Int.card_Icc]; omega

lemma rootBadResidues_density {p D : ℕ} (hD : 0 < D) (hpD : D ≤ p) :
    ((rootBadResidues p D).card : ℚ) / p ≤ 3 / D := by
  have hp : 0 < p := lt_of_lt_of_le hD hpD
  have hcard : ((rootBadResidues p D).card : ℚ) ≤ 2 * (((p - 1) / D : ℕ) : ℚ) + 1 := by
    exact_mod_cast rootBadResidues_card_le p D
  have hquot : ((((p - 1) / D : ℕ) : ℚ)) * D ≤ (p - 1 : ℕ) := by
    exact_mod_cast Nat.div_mul_le_self (p - 1) D
  have hpD' : (D : ℚ) ≤ p := by exact_mod_cast hpD
  have hsub : ((p - 1 : ℕ) : ℚ) ≤ p := by exact_mod_cast Nat.sub_le p 1
  have hD' : (0 : ℚ) < D := Nat.cast_pos.mpr hD
  have hp' : (0 : ℚ) < p := Nat.cast_pos.mpr hp
  rw [div_le_div_iff₀ hp' hD']
  nlinarith

/-- Because `p - 1 ≡ -1 mod p`, every near-collision forces the label itself
into the short interval of forbidden residues. -/
lemma root_collision_mem_bad {p D n : ℕ} (hp : 1 < p) (hD : 0 < D) (k : ℤ)
    (hcoll : |((p : ℚ) / (p - 1 : ℕ)) * D * k - D * n| ≤ 1) :
    (n : ZMod p) ∈ rootBadResidues p D := by
  let q := p - 1
  let d : ℤ := (p : ℤ) * k - (q : ℤ) * n
  have hq : 0 < q := by dsimp [q]; omega
  have hq' : (0 : ℚ) < q := Nat.cast_pos.mpr hq
  have hD' : (0 : ℚ) < D := Nat.cast_pos.mpr hD
  have heq : (d : ℚ) * D = (((p : ℚ) / q) * D * k - D * n) * q := by
    dsimp [d]
    push_cast
    field_simp
  have habs : (d.natAbs : ℚ) * D ≤ q := by
    calc
      _ = |(d : ℚ) * D| := by rw [abs_mul, abs_of_pos hD', Int.cast_natAbs, Int.cast_abs]
      _ = |(((p : ℚ) / q) * D * k - D * n) * q| := congrArg abs heq
      _ = |((p : ℚ) / q) * D * k - D * n| * q := by rw [abs_mul, abs_of_pos hq']
      _ ≤ 1 * q := mul_le_mul_of_nonneg_right hcoll hq'.le
      _ = _ := one_mul _
  have hnabs : d.natAbs ≤ q / D := (Nat.le_div_iff_mul_le hD).mpr (by exact_mod_cast habs)
  have hd : -((q / D : ℕ) : ℤ) ≤ d ∧ d ≤ ((q / D : ℕ) : ℤ) := by
    apply abs_le.mp
    rw [← Int.natCast_natAbs]
    exact_mod_cast hnabs
  have hres : (d : ZMod p) = (n : ZMod p) := by
    have hqeq : q + 1 = p := by dsimp [q]; omega
    have hqres : (q : ZMod p) = -1 := by
      have : (q : ZMod p) + 1 = 0 := by
        rw [← Nat.cast_add_one, hqeq, ZMod.natCast_self]
      linear_combination this
    dsimp [d]
    push_cast
    rw [ZMod.natCast_self, hqres]
    ring
  exact Finset.mem_image.mpr ⟨d, Finset.mem_Icc.mpr hd, hres⟩

lemma root_not_bad_separated {p D n : ℕ} (hp : 1 < p) (hD : 0 < D)
    (hn : (n : ZMod p) ∉ rootBadResidues p D) (k : ℤ) :
    1 < |((p : ℚ) / (p - 1 : ℕ)) * D * k - D * n| := by
  exact lt_of_not_ge (fun h => hn (root_collision_mem_bad hp hD k h))

end Erdos143
