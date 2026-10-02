import Erdos143.Definitions
import Mathlib.GroupTheory.Index
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Field

noncomputable section
open scoped BigOperators
namespace Erdos143

/-- A surjective homomorphism between finite additive groups preserves uniform density. -/
lemma preimage_density_of_surjective {G M : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    [AddGroup M] [Fintype M] [DecidableEq M] (f : G →+ M) (hf : Function.Surjective f)
    (S : Finset M) :
    ((Finset.univ.filter (fun x => f x ∈ S)).card : ℚ) / Fintype.card G =
      (S.card : ℚ) / Fintype.card M := by
  classical
  let K := (Finset.univ.filter (fun x => f x = 0)).card
  have hfiber (b : M) : (Finset.univ.filter (fun x => f x = b)).card = K :=
    AddMonoidHom.card_fiber_eq_of_mem_range f (hf b) (hf 0)
  have hall : Fintype.card G = Fintype.card M * K := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset G)) (t := (Finset.univ : Finset M))
      (f := f) (by intro x hx; exact Finset.mem_univ _)
    simpa only [Finset.card_univ, hfiber, Finset.sum_const, Finset.card_univ,
      smul_eq_mul] using h
  have hpart : (Finset.univ.filter (fun x => f x ∈ S)).card = S.card * K := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter (fun x => f x ∈ S)) (t := S) (f := f)
      (by intro x hx; exact (Finset.mem_filter.mp hx).2)
    have heq (b : M) (hb : b ∈ S) :
        {a ∈ Finset.univ.filter (fun x => f x ∈ S) | f a = b} =
          Finset.univ.filter (fun x => f x = b) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
      intro hxb
      simpa [hxb] using hb
    rw [h]
    calc
      _ = ∑ _b ∈ S, K := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [heq b hb, hfiber]
      _ = _ := by simp only [Finset.sum_const, smul_eq_mul]
  have hK : K ≠ 0 := by
    intro h
    have := Fintype.card_pos (α := G)
    simp [h] at hall
  rw [hpart, hall]
  push_cast
  exact mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr hK)

/-- Pulling back any set of residues to a multiple period keeps its density. -/
lemma zmod_preimage_density {L m : ℕ} [NeZero L] [NeZero m]
    (h : m ∣ L) (S : Finset (ZMod m)) :
    ((Finset.univ.filter (fun x : ZMod L => ZMod.castHom h (ZMod m) x ∈ S)).card : ℚ) / L =
      (S.card : ℚ) / m := by
  simpa only [ZMod.card] using preimage_density_of_surjective
    (ZMod.castHom h (ZMod m)).toAddMonoidHom (ZMod.castHom_surjective h) S

/-- The elementary union bound, expressed as the density of the complementary filter. -/
lemma complement_union_density {α ι : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
    (I : Finset ι) (B : ι → Finset α) :
    1 - ∑ i ∈ I, ((B i).card : ℚ) / Fintype.card α ≤
      (((I.biUnion B)ᶜ).card : ℚ) / Fintype.card α := by
  classical
  have hcard := (Finset.card_biUnion_le (s := I) (t := B))
  have hle := Finset.card_le_univ (I.biUnion B)
  have hpos : (0 : ℚ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  rw [Finset.card_compl, Nat.cast_sub hle, ← Finset.sum_div]
  apply (le_div_iff₀ hpos).mpr
  have hc : ((I.biUnion B).card : ℚ) ≤ ∑ i ∈ I, ((B i).card : ℚ) := by
    exact_mod_cast hcard
  field_simp
  linarith

end Erdos143
