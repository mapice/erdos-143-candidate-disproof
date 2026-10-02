import Erdos143.Definitions

open Filter
open scoped Topology

namespace Erdos143

/-- A lower limit along the real Abel parameter u→1 from below, expressed without
conditional completeness conventions for `liminf`. -/
def HasAbelLowerBound (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ a : ℝ, a < c → ∀ᶠ u : ℝ in 𝓝[<] 1, a ≤ f u

lemma hasAbelLowerBound_of_tendsto_minorant {f g : ℝ → ℝ} {c : ℝ}
    (hg : Tendsto g (𝓝[<] 1) (𝓝 c)) (hfg : ∀ᶠ u : ℝ in 𝓝[<] 1, g u ≤ f u) :
    HasAbelLowerBound f c := by
  intro a ha
  filter_upwards [hg.eventually (eventually_gt_nhds ha), hfg] with u hu hgu
  exact hu.le.trans hgu

lemma HasAbelLowerBound.mono {f g : ℝ → ℝ} {c : ℝ} (hf : HasAbelLowerBound f c)
    (hfg : ∀ᶠ u : ℝ in 𝓝[<] 1, f u ≤ g u) : HasAbelLowerBound g c := by
  intro a ha
  filter_upwards [hf a ha, hfg] with u hau hfu
  exact hau.trans hfu

lemma HasAbelLowerBound.add {f g : ℝ → ℝ} {a b : ℝ}
    (hf : HasAbelLowerBound f a) (hg : HasAbelLowerBound g b) :
    HasAbelLowerBound (fun u => f u + g u) (a + b) := by
  intro c hc
  let e := (a + b - c) / 2
  have he : 0 < e := by dsimp [e]; linarith
  filter_upwards [hf (a - e) (by linarith), hg (b - e) (by linarith)] with u hfu hgu
  dsimp [e] at hfu hgu
  linarith

lemma hasAbelLowerBound_of_tendsto {f : ℝ → ℝ} {a : ℝ} (hf : Tendsto f (𝓝[<] 1) (𝓝 a)) :
    HasAbelLowerBound f a := hasAbelLowerBound_of_tendsto_minorant hf (Eventually.of_forall (fun _ => le_rfl))

lemma HasAbelLowerBound.add_vanishing {f g : ℝ → ℝ} {a : ℝ}
    (hf : HasAbelLowerBound f a) (hg : Tendsto g (𝓝[<] 1) (𝓝 0)) :
    HasAbelLowerBound (fun u => f u + g u) a := by
  simpa only [add_zero] using hf.add (hasAbelLowerBound_of_tendsto hg)

lemma HasAbelLowerBound.mul_pos {f : ℝ → ℝ} {a b : ℝ} (hf : HasAbelLowerBound f a)
    (hb : 0 < b) : HasAbelLowerBound (fun u => b * f u) (b * a) := by
  intro c hc
  have hca : c / b < a := (div_lt_iff₀ hb).2 (by simpa [mul_comm] using hc)
  filter_upwards [hf (c / b) hca] with u hu
  have h := mul_le_mul_of_nonneg_left hu hb.le
  simpa only [mul_div_cancel₀ _ hb.ne'] using h

lemma HasAbelLowerBound.sum {ι : Type*} (S : Finset ι) {f : ι → ℝ → ℝ} {a : ι → ℝ}
    (h : ∀ i ∈ S, HasAbelLowerBound (f i) (a i)) :
    HasAbelLowerBound (fun u => ∑ i ∈ S, f i u) (∑ i ∈ S, a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (hasAbelLowerBound_of_tendsto (tendsto_const_nhds (x := (0 : ℝ))))
  | @insert i S hi ih =>
    simpa only [Finset.sum_insert hi] using (h i (by simp)).add
      (ih (fun j hj => h j (by simp [hj])))

lemma HasAbelLowerBound.mul_tendsto_pos {f g : ℝ → ℝ} {a b : ℝ}
    (hf : HasAbelLowerBound f a) (ha : 0 < a) (hg : Tendsto g (𝓝[<] 1) (𝓝 b)) (hb : 0 < b) :
    HasAbelLowerBound (fun u => g u * f u) (b * a) := by
  intro c hc
  have hgpos := hg.eventually (eventually_gt_nhds hb)
  by_cases hc0 : c < 0
  · filter_upwards [hf (a / 2) (by linarith), hgpos] with u hfu hgu
    have hfu0 : 0 ≤ f u := by linarith
    exact hc0.le.trans (mul_nonneg hgu.le hfu0)
  · have hc0' : 0 ≤ c := le_of_not_gt hc0
    let d := (c / b + a) / 2
    have hdiv : c / b < a := (div_lt_iff₀ hb).2 (by simpa [mul_comm] using hc)
    have hda : d < a := by dsimp [d]; linarith
    have hcd : c < b * d := by
      dsimp [d]
      have hcancel : b * (c / b) = c := by field_simp
      nlinarith
    have hgd := (hg.mul_const d).eventually (eventually_gt_nhds hcd)
    filter_upwards [hf d hda, hgpos, hgd] with u hfu hgu hprod
    exact hprod.le.trans (mul_le_mul_of_nonneg_left hfu hgu.le)

end Erdos143
