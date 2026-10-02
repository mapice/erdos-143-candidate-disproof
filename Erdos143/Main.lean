import Erdos143.RoundExtension
import Erdos143.LocalFiniteness

noncomputable section
open scoped BigOperators ENNReal
namespace Erdos143

/-- Classical choice is used only to select witnesses of the proved round-extension theorem. -/
def nextState (F : {F : ConstructionState // ValidState F}) :
    {F : ConstructionState // ValidState F} :=
  ⟨(round_extension_exists F.val F.property).choose,
    (round_extension_exists F.val F.property).choose_spec.1⟩

lemma nextState_properties (F : {F : ConstructionState // ValidState F}) :
    F.val.atoms ⊆ (nextState F).val.atoms ∧
      F.val.mass + (1 : ℝ≥0∞) / 576 ≤ (nextState F).val.mass := by
  exact ⟨(round_extension_exists F.val F.property).choose_spec.2.1,
    (round_extension_exists F.val F.property).choose_spec.2.2.2⟩

def stateSequence : ℕ → {F : ConstructionState // ValidState F}
  | 0 => ⟨emptyState, emptyState_valid⟩
  | n + 1 => nextState (stateSequence n)

def pointSequence (n : ℕ) : Set ℚ := ((stateSequence n).val.points : Set ℚ)

def constructedSet : Set ℚ := ⋃ n, pointSequence n

lemma pointSequence_monotone : Monotone pointSequence := by
  apply monotone_nat_of_le_succ
  intro n a ha
  change a ∈ (stateSequence (n + 1)).val.points
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  apply Finset.mem_image.mpr
  exact ⟨b, (nextState_properties (stateSequence n)).1 hb, rfl⟩

lemma stateSequence_mass_lower (n : ℕ) :
    (n : ℝ≥0∞) / 576 ≤ (stateSequence n).val.mass := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      (n.succ : ℝ≥0∞) / 576 = (n : ℝ≥0∞) / 576 + 1 / 576 := by
        rw [Nat.cast_succ]
        simp only [div_eq_mul_inv, add_mul, one_mul]
      _ ≤ (stateSequence n).val.mass + 1 / 576 := add_le_add_right ih _
      _ ≤ (stateSequence n.succ).val.mass := (nextState_properties (stateSequence n)).2

lemma constructedSet_original : Original constructedSet :=
  original_iUnion_of_monotone pointSequence_monotone (fun n => (stateSequence n).property.original)

lemma constructedSet_lower : ∀ a ∈ constructedSet, (2 : ℚ) ≤ a :=
  lower_bound_iUnion (fun n => (stateSequence n).property.lower)

lemma constructedSet_tiny : ∀ a ∈ constructedSet, TinyPositiveDisplacement a := by
  intro a ha
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
  exact (stateSequence n).property.tiny a hn

lemma constructedSet_weight_diverges : totalWeight constructedSet = ⊤ := by
  apply totalWeight_iUnion_eq_top_of_unbounded
  intro n
  refine ⟨(n + 1) * 576, ?_⟩
  have hmass := stateSequence_mass_lower ((n + 1) * 576)
  have heq : (((n + 1) * 576 : ℕ) : ℝ≥0∞) / 576 = (n : ℝ≥0∞) + 1 := by
    push_cast
    exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
  rw [heq] at hmass
  have hlt : (n : ℝ≥0∞) < (n : ℝ≥0∞) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (show (n : ℝ≥0∞) < ((n + 1 : ℕ) : ℝ≥0∞) by exact_mod_cast Nat.lt_succ_self n)
  change (n : ℝ≥0∞) < totalWeight ((stateSequence ((n + 1) * 576)).val.points : Set ℚ)
  rw [totalWeight_finset]
  exact hlt.trans_le hmass

/-- The exact requested existence theorem, with no unproved analytic or construction interface. -/
theorem mainConclusion_proved : MainConclusion := by
  exact ⟨constructedSet, rational_set_countable _, constructedSet_lower,
    constructedSet_original, constructedSet_weight_diverges⟩

/-- The stronger manuscript conclusion also includes local finiteness and the
specified twelfth-power positive displacement from the integer lattice. -/
theorem strongConclusion_proved : StrongConclusion := by
  exact ⟨constructedSet, rational_set_countable _, constructedSet_lower,
    constructedSet_original, constructedSet_weight_diverges,
    original_locallyFiniteAbove constructedSet_original constructedSet_lower,
    constructedSet_tiny⟩

end Erdos143
