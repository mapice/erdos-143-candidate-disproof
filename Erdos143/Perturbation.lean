import Erdos143.Definitions

namespace Erdos143

/-- The chosen denominator gives the exact twelfth-power displacement bound. -/
lemma perturbation_bound {m U q : ℕ} (hm : 2 ≤ m) (hmU : m ≤ U)
    (hq : 2 * U ^ 13 ≤ q) :
    (m : ℚ) / q ≤ 1 / (2 * (m : ℚ) ^ 12) := by
  have hm0 : (0 : ℚ) < m := by exact_mod_cast (by omega : 0 < m)
  have hU0 : 0 < U := by omega
  have hq0 : 0 < q := by
    have hpow : 0 < U ^ 13 := pow_pos hU0 _
    omega
  have hq0q : (0 : ℚ) < q := by exact_mod_cast hq0
  have hp : m ^ 13 ≤ U ^ 13 := Nat.pow_le_pow_left hmU 13
  have hpq : (m : ℚ) ^ 13 ≤ (U : ℚ) ^ 13 := by exact_mod_cast hp
  have hqq : 2 * (U : ℚ) ^ 13 ≤ q := by exact_mod_cast hq
  apply (div_le_div_iff₀ hq0q (by positivity : (0 : ℚ) < 2 * (m : ℚ) ^ 12)).2
  nlinarith [show (m : ℚ) ^ 13 = (m : ℚ) ^ 12 * m from pow_succ _ _]

lemma perturbed_point_tiny {m U q : ℕ} (hm : 2 ≤ m) (hmU : m ≤ U)
    (hq : 2 * U ^ 13 ≤ q) : TinyPositiveDisplacement ((m : ℚ) + (m : ℚ) / q) := by
  refine ⟨m, hm, ?_, ?_⟩
  · have hm0 : (0 : ℚ) < m := by exact_mod_cast (by omega : 0 < m)
    have hU0 : 0 < U := by omega
    have hq0 : 0 < q := by
      have hpow : 0 < U ^ 13 := pow_pos hU0 _
      omega
    have hq0q : (0 : ℚ) < q := by exact_mod_cast hq0
    simpa using div_pos hm0 hq0q
  · simpa using perturbation_bound hm hmU hq

end Erdos143
