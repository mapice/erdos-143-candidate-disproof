import Erdos143.ProgressionScaling
import Erdos143.CoprimeAbel

noncomputable section
open Filter
open scoped Topology ArithmeticFunction.Omega

namespace Erdos143

lemma scaled_progression_abel_lower_bound {g M c : ℕ} [NeZero M] (hg : 1 ≤ g)
    (hc : IsUnit (c : ZMod M)) :
    HasAbelLowerBound
      (fun u : ℝ => (1 - u) * progressionMass (g * M) ((g * c : ℕ) : ZMod (g * M)) u)
      (1 / (4 * ((g * M : ℕ) : ℝ))) := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hMR : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hbase := coprime_progression_abel_lower_bound hc
  have hid : Tendsto (fun u : ℝ => u) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
  have hcoef : Tendsto (fun u : ℝ => u ^ Ω g / (g : ℝ)) (𝓝[<] 1) (𝓝 (1 / (g : ℝ))) := by
    simpa only [one_pow] using (hid.pow (Ω g)).div_const (g : ℝ)
  have hmul := hbase.mul_tendsto_pos (by positivity : (0 : ℝ) < 1 / (4 * (M : ℝ)))
    hcoef (by positivity : (0 : ℝ) < 1 / (g : ℝ))
  have herr : Tendsto (fun u : ℝ => -(1 - u) * shiftPenalty g) (𝓝[<] 1) (𝓝 0) := by
    simpa using (((tendsto_const_nhds (x := (1 : ℝ))).sub hid).neg).mul_const (shiftPenalty g)
  have hbound := hmul.add_vanishing herr
  have hconst : (1 / (g : ℝ)) * (1 / (4 * (M : ℝ))) = 1 / (4 * ((g * M : ℕ) : ℝ)) := by
    push_cast
    field_simp
  rw [hconst] at hbound
  apply hbound.mono
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with u hu
  have h := mul_le_mul_of_nonneg_left (progressionMass_scale_lower (M := M) (c := c) hg hu.1.le hu.2)
    (show 0 ≤ 1 - u by linarith [hu.2])
  convert h using 1
  ring

/-- The positive Abel lower bound includes every residue, with no coprimality omission. -/
lemma all_residues_abel_lower_bound (N : ℕ) [NeZero N] (b : ZMod N) :
    HasAbelLowerBound (fun u : ℝ => (1 - u) * progressionMass N b u) (1 / (4 * (N : ℝ))) := by
  let n : ℕ := b.val
  let g : ℕ := Nat.gcd n N
  let M : ℕ := N / g
  let c : ℕ := n / g
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right n (NeZero.pos N)
  have hM0 : 0 < M := Nat.div_pos (Nat.gcd_le_right n (NeZero.pos N)) hg0
  letI : NeZero M := ⟨hM0.ne'⟩
  have hcop : Nat.Coprime c M := Nat.coprime_div_gcd_div_gcd hg0
  have hc : IsUnit (c : ZMod M) := (ZMod.isUnit_iff_coprime c M).2 hcop
  have h := scaled_progression_abel_lower_bound (g := g) (M := M) (c := c) (by omega) hc
  have hN : g * M = N := Nat.mul_div_cancel' (Nat.gcd_dvd_right n N)
  have hn : g * c = n := Nat.mul_div_cancel' (Nat.gcd_dvd_left n N)
  have hfun : (fun u : ℝ => (1 - u) * progressionMass (g * M) ((g * c : ℕ) : ZMod (g * M)) u) =
      fun u : ℝ => (1 - u) * progressionMass N b u := by
    funext u
    congr 1
    calc
      _ = progressionMass N (n : ZMod N) u := progressionMass_natCast_congr hN hn u
      _ = _ := by rw [show (n : ZMod N) = b from ZMod.natCast_zmod_val b]
  rw [hfun] at h
  simpa only [hN] using h

end Erdos143
