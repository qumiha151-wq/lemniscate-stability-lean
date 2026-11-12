import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! A direct FTC estimate on the oscillation inside one interval. -/
noncomputable section
open MeasureTheory Set
namespace LengthGrowth

theorem interval_oscillation_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f f' : ℝ → E} {a b s t : ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (hc : Continuous f')
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖f s-f t‖ ≤ ∫ x in a..b, ‖f' x‖ := by
  have hforward : ∀ u v, u ∈ Icc a b → v ∈ Icc a b → u ≤ v →
      ‖f v-f u‖ ≤ ∫ x in a..b, ‖f' x‖ := by
    intro u v hu hv huv
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hd x) (hc.intervalIntegrable u v)
    rw [← hi]
    exact (intervalIntegral.norm_integral_le_integral_norm huv).trans
      (intervalIntegral.integral_mono_interval hu.1 huv hv.2
        (Filter.Eventually.of_forall (fun x => norm_nonneg (f' x)))
        (hc.norm.intervalIntegrable _ _))
  rcases le_total s t with hst | hts
  · rw [norm_sub_rev]
    exact hforward s t hs ht hst
  · exact hforward t s ht hs hts

end LengthGrowth

open Lean Elab Command in
run_cmd do
  for axiomName in (← collectAxioms `LengthGrowth.interval_oscillation_le) do
    unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
      throwError "Interval oscillation axiom audit failed: {axiomName}"
  logInfo "LengthGrowth interval oscillation audit passed."
