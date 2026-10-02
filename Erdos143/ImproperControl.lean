import Erdos143.Definitions
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Set

namespace Erdos143

/-- A reusable improper-integrability criterion with a power bound at zero and exponential
bound at infinity, avoiding any assertion that boundedness alone implies integrability. -/
lemma integrableOn_Ioi_of_power_exp_bounds {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Ioi 0)) {eps a C D E c : ℝ}
    (heps : 0 < eps) (_heps1 : eps ≤ 1) (ha : -1 < a) (hc : 0 < c)
    (hsmall : ∀ t, 0 < t → t ≤ eps → ‖f t‖ ≤ C * t ^ a + D)
    (htail : ∀ t, 1 ≤ t → ‖f t‖ ≤ E * Real.exp ((-c) * t)) :
    IntegrableOn f (Ioi 0) := by
  have hsmall_cont : ContinuousOn f (Ioo 0 eps) := hcont.mono Ioo_subset_Ioi_self
  have hp : IntegrableOn (fun t : ℝ => t ^ a) (Ioo 0 eps) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff heps).2 ha
  have hconst : IntegrableOn (fun _ : ℝ => D) (Ioo 0 eps) :=
    (continuous_const.integrableOn_Icc (a := (0 : ℝ)) (b := eps)).mono_set Ioo_subset_Icc_self
  have hsmall_int : IntegrableOn f (Ioo 0 eps) :=
    ((hp.const_mul C).add hconst).mono' (hsmall_cont.aestronglyMeasurable measurableSet_Ioo)
      (ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => hsmall t ht.1 ht.2.le))
  have hmid_cont : ContinuousOn f (Icc eps 1) := hcont.mono (by
    intro t ht
    exact heps.trans_le ht.1)
  have hmid_int : IntegrableOn f (Icc eps 1) := hmid_cont.integrableOn_Icc
  have htail_cont : ContinuousOn f (Ioi 1) := hcont.mono (Ioi_subset_Ioi (by norm_num))
  have htail_int : IntegrableOn f (Ioi 1) :=
    ((integrableOn_exp_mul_Ioi (by linarith : -c < 0) 1).const_mul E).mono'
      (htail_cont.aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => htail t ht.le))
  apply ((hsmall_int.union hmid_int).union htail_int).mono_set
  intro t ht
  by_cases hteps : t < eps
  · exact Or.inl (Or.inl ⟨ht, hteps⟩)
  · by_cases ht1 : t ≤ 1
    · exact Or.inl (Or.inr ⟨le_of_not_gt hteps, ht1⟩)
    · exact Or.inr (lt_of_not_ge ht1)

end Erdos143
