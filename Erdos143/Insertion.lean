import Erdos143.Geometry

namespace Erdos143

/-- All separation obligations for inserting one finite or infinite primitive block.
This lemma proves the geometric implication only; it does not assume or assert the
existence of parameters satisfying the hypotheses. -/
lemma insert_primitive_block_original {F : Set ℚ} {P : Set ℕ} {D : ℕ} {c : ℚ}
    (hF : Original F) (hP : Primitive P) (hD : 1 ≤ D) (hc : 1 < c)
    (hfree : ∀ n ∈ P, RightFree F D n)
    (hshift : ∀ n ∈ P, 0 < (c - 1) * D * n)
    (hsmall : ∀ a ∈ F, ∀ n ∈ P, (c - 1) * D * n < 1 / (a.den : ℚ))
    (habove : ∀ a ∈ F, ∀ n ∈ P, a + 1 < c * D * n)
    (hnonneg : ∀ n ∈ P, 0 ≤ c * D * n) :
    Original (F ∪ ((fun n : ℕ => c * D * n) '' P)) := by
  have hDq : (1 : ℚ) ≤ D := by exact_mod_cast hD
  have hcD : 1 ≤ c * D := by nlinarith
  apply original_union hF (scaled_primitive_original hP hcD)
  · intro a ha b hb k hk
    obtain ⟨n, hn, rfl⟩ := hb
    have hf := hfree n hn a ha
    have hpert := old_source_perturbation_safe (A := a.num) (B := a.den)
      (m := (D : ℤ) * n) (η := (c - 1) * D * n) a.den_pos
    have hf' : ∀ j : ℤ, ¬ ((-1 : ℚ) < j * ((a.num : ℚ) / a.den) -
        ((D : ℤ) * n : ℤ) ∧ j * ((a.num : ℚ) / a.den) - ((D : ℤ) * n : ℤ) ≤ 1) := by
      simpa only [Rat.num_div_den, Int.cast_mul, Int.cast_natCast] using hf
    have h := hpert hf' (hshift n hn) (hsmall a ha n hn) (k : ℤ)
    simp only [Rat.num_div_den, Int.cast_natCast, Int.cast_mul] at h
    convert h.le using 2
    ring
  · intro b hb a ha k hk
    obtain ⟨n, hn, rfl⟩ := hb
    exact (new_source_separated (hnonneg n hn) (habove a ha n hn) hk).le

end Erdos143
