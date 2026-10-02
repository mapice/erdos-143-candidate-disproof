import Erdos143.Definitions
import Mathlib.Data.Nat.Prime.Infinite

namespace Erdos143

lemma prime_not_dvd_finset_prod {α : Type*} (S : Finset α) (f : α → ℕ) {H : ℕ}
    (hH : H.Prime) (hS : ∀ x ∈ S, ¬ H ∣ f x) : ¬ H ∣ ∏ x ∈ S, f x := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hH.not_dvd_one
  | @insert x S hx ih =>
    rw [Finset.prod_insert hx]
    exact hH.not_dvd_mul (hS x (by simp)) (ih (fun y hy => hS y (by simp [hy])))

/-- A single prime can exceed every member of any finite threshold list. -/
lemma exists_prime_above_finset (S : Finset ℕ) :
    ∃ H : ℕ, H.Prime ∧ ∀ x ∈ S, x < H := by
  obtain ⟨H, hlarge, hprime⟩ := Nat.exists_infinite_primes (S.sup id + 1)
  refine ⟨H, hprime, ?_⟩
  intro x hx
  have hxle : x ≤ S.sup id := Finset.le_sup (f := id) hx
  omega

/-- The current invariant forbids each private prime in every newly stored nonprivate part. -/
lemma private_prime_preserved {H G D n : ℕ} (hH : H.Prime)
    (hG : ¬ H ∣ G) (hD : ¬ H ∣ D) (hn : ¬ H ∣ n) : ¬ H ∣ G * D * n :=
  hH.not_dvd_mul (hH.not_dvd_mul hG hD) hn

/-- Choosing the new prime above all positive stored parts handles the reverse direction. -/
lemma fresh_prime_avoids_old_part {H N : ℕ} (hN : 0 < N) (hHN : N < H) : ¬ H ∣ N :=
  Nat.not_dvd_of_pos_of_lt hN hHN

/-- A product of the stored parts may replace their lcm. This proves the existence of
an arbitrarily large grid divisible by every stored part and avoiding every private prime. -/
lemma exists_private_compatible_grid (N H : Finset ℕ)
    (hN : ∀ n ∈ N, 0 < n) (hH : ∀ h ∈ H, h.Prime ∧ 2 < h)
    (havoid : ∀ h ∈ H, ∀ n ∈ N, ¬ h ∣ n) (M : ℕ) :
    ∃ D : ℕ, M < D ∧ 48 ≤ D ∧ (∀ n ∈ N, n ∣ D) ∧ ∀ h ∈ H, ¬ h ∣ D := by
  classical
  let Q : ℕ := ∏ n ∈ N, n
  have hQ : 0 < Q := Finset.prod_pos hN
  obtain ⟨v, hv⟩ := pow_unbounded_of_one_lt (max M 48) (by decide : 1 < (2 : ℕ))
  refine ⟨2 ^ v * Q, ?_, ?_, ?_, ?_⟩
  · nlinarith [le_max_left M 48]
  · nlinarith [le_max_right M 48]
  · intro n hn
    exact (Finset.dvd_prod_of_mem id hn).trans (dvd_mul_left Q (2 ^ v))
  · intro h hh
    have hprime := (hH h hh).1
    have hnot2 : ¬ h ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) (hH h hh).2
    have hnotpow : ¬ h ∣ 2 ^ v := fun hd => hnot2 (hprime.dvd_of_dvd_pow hd)
    have hnotQ : ¬ h ∣ Q := prime_not_dvd_finset_prod N id hprime (havoid h hh)
    exact hprime.not_dvd_mul hnotpow hnotQ

end Erdos143
