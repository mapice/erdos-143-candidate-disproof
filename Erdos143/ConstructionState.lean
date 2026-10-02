import Erdos143.Arithmetic
import Erdos143.Geometry
import Erdos143.Perturbation
import Erdos143.BlockWeight
import Erdos143.RoundLabels

noncomputable section
open scoped BigOperators ENNReal
namespace Erdos143

/-- Stored arithmetic data: the private prime, the nonprivate numerator part,
and the positive denominator. -/
structure StoredPoint where
  H : ℕ
  N : ℕ
  q : ℕ
  deriving DecidableEq

def StoredPoint.value (a : StoredPoint) : ℚ := a.H * a.N / a.q

structure ConstructionState where
  atoms : Finset StoredPoint
  primes : Finset ℕ
  deriving DecidableEq

def ConstructionState.points (F : ConstructionState) : Finset ℚ := F.atoms.image StoredPoint.value

def ConstructionState.mass (F : ConstructionState) : ℝ≥0∞ := ∑ a ∈ F.points, weight a

/-- Every field is a proved invariant of the finite construction, not an assumption
exported by the final theorem. -/
structure ValidState (F : ConstructionState) : Prop where
  prime : ∀ h ∈ F.primes, h.Prime ∧ 2 < h
  budget : (∑ h ∈ F.primes, (1 : ℚ) / h) < 1 / 100
  data : ∀ a ∈ F.atoms, a.H ∈ F.primes ∧ 0 < a.N ∧ 0 < a.q ∧
    ¬ a.H ∣ a.q ∧ 4 < a.value / a.H
  avoid : ∀ h ∈ F.primes, ∀ a ∈ F.atoms, ¬ h ∣ a.N
  lower : ∀ a ∈ F.points, (2 : ℚ) ≤ a
  original : Original (F.points : Set ℚ)
  tiny : ∀ a ∈ F.points, TinyPositiveDisplacement a

def emptyState : ConstructionState := ⟨∅, ∅⟩

lemma emptyState_valid : ValidState emptyState := by
  constructor
  · simp [emptyState]
  · norm_num [emptyState]
  · simp [emptyState]
  · simp [emptyState]
  · simp [emptyState, ConstructionState.points]
  · simpa [emptyState, ConstructionState.points] using original_empty
  · simp [emptyState, ConstructionState.points]

lemma state_grid_exists (F : ConstructionState) (hF : ValidState F) :
    ∃ D : ℕ, 48 ≤ D ∧ (∀ a ∈ F.atoms, a.N ∣ D) ∧
      ∀ h ∈ F.primes, ¬ h ∣ D := by
  obtain ⟨D, _, hD, hdiv, hav⟩ := exists_private_compatible_grid
    (F.atoms.image StoredPoint.N) F.primes
    (by intro n hn; obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn; exact (hF.data a ha).2.1)
    hF.prime
    (by intro h hh n hn; obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn; exact hF.avoid h hh a ha) 0
  exact ⟨D, hD, fun a ha => hdiv a.N (Finset.mem_image.mpr ⟨a, ha, rfl⟩), hav⟩

/-- A reset grid excludes all earlier-round collisions whenever the label avoids
the stored private prime. -/
lemma stored_point_grid_separated (a : StoredPoint) (hH : a.H.Prime)
    (hq : 0 < a.q) (hHq : ¬ a.H ∣ a.q)
    (hsize : 4 < a.value / a.H) {D n : ℕ} (hdiv : a.N ∣ D)
    (hHD : ¬ a.H ∣ D) (hHn : ¬ a.H ∣ n) (k : ℤ) :
    4 < |k * a.value - D * n| := by
  let t := D / a.N
  have hDt : a.N * t = D := Nat.mul_div_cancel' hdiv
  have hHt : ¬ a.H ∣ t := by
    intro ht
    apply hHD
    rw [← hDt]
    exact dvd_mul_of_dvd_right ht _
  apply private_grid_separated hH hHt hHq hHn hsize
  unfold StoredPoint.value
  have hq' : (a.q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hq)
  have hDt' : (a.N : ℚ) * t = D := by exact_mod_cast hDt
  field_simp
  nlinarith [hDt']

lemma state_grid_free (F : ConstructionState) (hF : ValidState F)
    {D n : ℕ} (hdiv : ∀ a ∈ F.atoms, a.N ∣ D)
    (hHD : ∀ h ∈ F.primes, ¬ h ∣ D)
    (hn : ∀ h ∈ F.primes, ¬ h ∣ n) : RightFree (F.points : Set ℚ) D n := by
  intro x hx k hcoll
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨haH, _, haq, haHq, hasize⟩ := hF.data a ha
  have h := stored_point_grid_separated a (hF.prime a.H haH).1 haq haHq hasize
    (hdiv a ha) (hHD a.H haH) (hn a.H haH) k
  have hle : |(k : ℚ) * a.value - D * n| ≤ 1 := abs_le.mpr ⟨hcoll.1.le, hcoll.2⟩
  linarith

/-- A fresh private prime can satisfy any finite size requirements while preserving
the strict reciprocal budget. -/
lemma fresh_private_prime (F : ConstructionState) (hF : ValidState F) (M : ℕ) :
    ∃ H : ℕ, H.Prime ∧ M < H ∧ 2 < H ∧ H ∉ F.primes ∧
      (∀ a ∈ F.atoms, a.N < H) ∧
      (∑ h ∈ insert H F.primes, (1 : ℚ) / h) < 1 / 100 := by
  let eps : ℚ := 1 / 100 - ∑ h ∈ F.primes, (1 : ℚ) / h
  have heps : 0 < eps := sub_pos.mpr hF.budget
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / eps)
  obtain ⟨H, hprime, hlarge⟩ := exists_prime_above_finset
    (insert K (insert M (insert 2 (F.primes ∪ F.atoms.image StoredPoint.N))))
  have hHM : M < H := hlarge M (by simp)
  have hH2 : 2 < H := hlarge 2 (by simp)
  have hnot : H ∉ F.primes := by
    intro hh
    exact (lt_irrefl H) (hlarge H (by simp [hh]))
  refine ⟨H, hprime, hHM, hH2, hnot, ?_, ?_⟩
  · intro a ha
    exact hlarge a.N (by simp [Finset.mem_image_of_mem StoredPoint.N ha])
  · rw [Finset.sum_insert hnot]
    have hHK : (K : ℚ) < H := by exact_mod_cast hlarge K (by simp)
    have hHpos : (0 : ℚ) < H := Nat.cast_pos.mpr hprime.pos
    have hi : (1 : ℚ) / H < eps := (div_lt_iff₀ hHpos).mpr (by
      have := (div_lt_iff₀ heps).mp (hK.trans hHK)
      nlinarith)
    dsimp [eps] at hi
    linarith

end Erdos143
