import Erdos143.Progressions
import Erdos143.PrincipalAbel
import Erdos143.NonprincipalAbel

noncomputable section
open Filter Complex
open scoped BigOperators Topology

namespace Erdos143

def characterError {N : ℕ} [NeZero N] (b : ZMod N) (u : ℝ) : ℂ := by
  classical
  exact ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ N)).erase 1,
    χ b⁻¹ * ((1 - (u : ℂ)) * integratedGeneratingValue χ u)

lemma characterError_tendsto_zero {N : ℕ} [NeZero N] (b : ZMod N) :
    Tendsto (characterError b) (𝓝[<] 1) (𝓝 0) := by
  classical
  have h := tendsto_finset_sum ((Finset.univ : Finset (DirichletCharacter ℂ N)).erase 1)
    (fun χ hχ => (nonprincipal_normalized_integral_tendsto_zero χ (Finset.mem_erase.mp hχ).1).const_mul (χ b⁻¹))
  simpa only [characterError, mul_zero, Finset.sum_const_zero] using h

lemma normalized_progression_identity {N : ℕ} [NeZero N] {b : ZMod N} (hb : IsUnit b)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (1 - u) * progressionMass N b u = (N.totient : ℝ)⁻¹ *
      ((1 - u) * (integratedGeneratingValue (1 : DirichletCharacter ℂ N) u).re + (characterError b u).re) := by
  classical
  have horth := progressionMass_orthogonality hb hu0 hu1
  have hcomplex : (1 - (u : ℂ)) * (progressionMass N b u : ℂ) = (N.totient : ℂ)⁻¹ *
      ((1 - (u : ℂ)) * integratedGeneratingValue (1 : DirichletCharacter ℂ N) u + characterError b u) := by
    calc
      _ = (N.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ N,
          χ b⁻¹ * ((1 - (u : ℂ)) * integratedGeneratingValue χ u) := by
        rw [horth, mul_left_comm (1 - (u : ℂ)) (N.totient : ℂ)⁻¹, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro χ _
        ring
      _ = _ := by
        congr 1
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ N))]
        simp only [principal_character_inverse_unit hb, one_mul]
        exact add_comm _ _
  have hphi : (N.totient : ℂ)⁻¹ = (((N.totient : ℝ)⁻¹ : ℝ) : ℂ) := by simp
  have huco : 1 - (u : ℂ) = ((1 - u : ℝ) : ℂ) := by push_cast; rfl
  rw [hphi, huco] at hcomplex
  have hreal := congrArg Complex.re hcomplex
  simpa only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero] using hreal

/-- The required positive Abel lower bound in every invertible residue class. -/
lemma coprime_progression_abel_lower_bound {N : ℕ} [NeZero N] {b : ZMod N} (hb : IsUnit b) :
    HasAbelLowerBound (fun u : ℝ => (1 - u) * progressionMass N b u) (1 / (4 * (N : ℝ))) := by
  have hE : Tendsto (fun u => (characterError b u).re) (𝓝[<] 1) (𝓝 0) := by
    simpa using (continuous_re.tendsto 0).comp (characterError_tendsto_zero b)
  have hφ : (0 : ℝ) < N.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos N)
  have hscaled := ((principal_abel_lower_bound N).add_vanishing hE).mul_pos (inv_pos.mpr hφ)
  have heq : (N.totient : ℝ)⁻¹ * (totientRatio N / 4) = 1 / (4 * (N : ℝ)) := by
    have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
    unfold totientRatio
    field_simp
  rw [heq] at hscaled
  apply hscaled.mono
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with u hu
  exact (normalized_progression_identity hb hu.1.le hu.2).symm.le

end Erdos143
