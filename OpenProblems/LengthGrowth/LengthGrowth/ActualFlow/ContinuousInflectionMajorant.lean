import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace LengthGrowth.ActualFlow.TurningEnvelope

/-- An integrable upper semicontinuous bound on a time tail admits a
    continuous integrable majorant on the tail starting one unit later. -/
theorem exists_continuous_integrable_tail_majorant {P : ℝ → ℝ} {T : ℝ}
    (usc : UpperSemicontinuousOn P (Ioi T)) (nonneg : ∀ t > T, 0 ≤ P t)
    (intP : IntegrableOn P (Ioi T)) :
    ∃ r : ℝ → ℝ, Continuous r ∧ IntegrableOn r (Ioi (T + 1)) ∧
      (∀ t, 0 ≤ r t) ∧ ∀ t > T + 1, P t ≤ r t := by
  let a := T + 1
  have Ta : T < a := lt_add_one T
  let f := fun t => P (max a t)
  have fpos (t) : 0 ≤ f t := nonneg _ (Ta.trans_le (le_max_left ..))
  have fusc : UpperSemicontinuous f := upperSemicontinuousOn_univ_iff.mp <|
    usc.comp (continuous_const.max continuous_id).continuousOn
      (fun t _ => Ta.trans_le (le_max_left a t))
  have fi : IntegrableOn f (Ioi a) := (intP.mono_set (Ioi_subset_Ioi Ta.le)).congr_fun
    (fun t ht => by simp only [f, max_eq_right (show a < t from ht).le]) measurableSet_Ioi
  let μ : Measure ℝ := volume.restrict (Ioi a)
  obtain ⟨g, above, glsc, gi, gfinite, _⟩ :=
    exists_lt_lowerSemicontinuous_integral_lt (μ := μ) f fi zero_lt_one
  let band := fun t => {c : ℝ | f t < c ∧ (c : EReal) < g t}
  have convex (t) : Convex ℝ (band t) := by
    apply convex_iff_ordConnected.mpr
    refine ⟨fun _ hx _ hy _ hz => ?_⟩
    exact ⟨hx.1.trans_le hz.1, (EReal.coe_le_coe_iff.mpr hz.2).trans_lt hy.2⟩
  have localBand (t) : ∃ c : ℝ, ∀ᶠ u in 𝓝 t, c ∈ band u := by
    obtain ⟨c, lo, hi⟩ := EReal.exists_between_coe_real (above t)
    exact ⟨c, (fusc t c (EReal.coe_lt_coe_iff.mp lo)).and (glsc t (c : EReal) hi)⟩
  obtain ⟨r, hr⟩ := exists_continuous_forall_mem_convex_of_local_const convex localBand
  have rpos (t) : 0 ≤ r t := (fpos t).trans (hr t).1.le
  refine ⟨r, r.continuous, gi.mono' r.continuous.aestronglyMeasurable ?_, rpos, ?_⟩
  · filter_upwards [gfinite] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (rpos t)]
    simpa only [EReal.toReal_coe] using
      EReal.toReal_le_toReal (hr t).2.le (EReal.coe_ne_bot _) ht.ne
  · intro t ht
    simpa only [f, max_eq_right (show a < t from ht).le] using (hr t).1.le

end LengthGrowth.ActualFlow.TurningEnvelope
#print axioms LengthGrowth.ActualFlow.TurningEnvelope.exists_continuous_integrable_tail_majorant
