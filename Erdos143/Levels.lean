import Erdos143.Definitions

noncomputable section
open scoped ArithmeticFunction.Omega

namespace Erdos143

/-- Every positive Ω level is primitive; multiplicities are counted. -/
lemma omega_level_primitive {r : ℕ} (hr : 0 < r) :
    Primitive {n : ℕ | Ω n = r} := by
  intro m hm n hn hdiv
  have hm0 : m ≠ 0 := by
    intro hmz
    subst m
    simp only [Set.mem_setOf_eq, ArithmeticFunction.cardFactors_zero] at hm
    omega
  have hn0 : n ≠ 0 := by
    intro hnz
    subst n
    simp only [Set.mem_setOf_eq, ArithmeticFunction.cardFactors_zero] at hn
    omega
  obtain ⟨k, rfl⟩ := hdiv
  have hk0 : k ≠ 0 := by
    intro hk
    simp [hk] at hn0
  have hmul := ArithmeticFunction.cardFactors_mul hm0 hk0
  have hkΩ : Ω k = 0 := by
    simp only [Set.mem_setOf_eq] at hm hn
    omega
  have hk1 : k = 1 :=
    (ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one.mp hkΩ).resolve_left hk0
  simp [hk1]

lemma primitive_mono {P Q : Set ℕ} (hQ : Primitive Q) (hPQ : P ⊆ Q) : Primitive P := by
  intro m hm n hn hdiv
  exact hQ m (hPQ hm) n (hPQ hn) hdiv

/-- Therefore any finite truncation or residue restriction of a positive level is primitive. -/
lemma primitive_of_constant_omega {P : Set ℕ} {r : ℕ} (hr : 0 < r)
    (hP : ∀ n ∈ P, Ω n = r) : Primitive P :=
  primitive_mono (omega_level_primitive hr) hP

end Erdos143
