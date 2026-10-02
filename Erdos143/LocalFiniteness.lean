import Erdos143.Definitions

namespace Erdos143

/-- The unit-distance condition at k = 1 already makes integer parts injective. -/
lemma original_floor_injOn {A : Set ℚ} (hA : Original A) : Set.InjOn Int.floor A := by
  intro a ha b hb hab
  by_contra hne
  have hdist := hA a ha b hb hne 1 (by omega)
  norm_num at hdist
  have hla := Int.floor_le a
  have hlb := Int.floor_le b
  have hua := Int.lt_floor_add_one a
  have hub := Int.lt_floor_add_one b
  rw [hab] at hla hua
  have hsmall : |a - b| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  linarith

/-- In the lower-bounded setting no separate growth assumption is needed for local finiteness. -/
lemma original_locallyFiniteAbove {A : Set ℚ} (hA : Original A)
    (hlower : ∀ a ∈ A, (2 : ℚ) ≤ a) : LocallyFiniteAbove A := by
  intro x
  have hmap : Set.MapsTo Int.floor (A ∩ Set.Iic x) (Set.Icc (2 : ℤ) ⌊x⌋) := by
    intro a ha
    constructor
    · simpa using Int.floor_mono (hlower a ha.1)
    · exact Int.floor_mono ha.2
  exact (Set.finite_Icc (2 : ℤ) ⌊x⌋).of_injOn hmap
    ((original_floor_injOn hA).mono Set.inter_subset_left)

end Erdos143
