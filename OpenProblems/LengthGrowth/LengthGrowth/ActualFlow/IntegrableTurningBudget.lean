import LengthGrowth.ActualFlow.MaterialTurnPrimitives
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
open Set Function MeasureTheory Filter
open scoped Topology
namespace LengthGrowth.ActualFlow.TurningEnvelope

theorem small_tail_budget {T : ℝ} {r : ℝ→ℝ} (cr : Continuous r)
    (ir : IntegrableOn r (Ioi T)) : ∃ a, 0<a ∧ T<a ∧ ∃ B : ℝ→ℝ,
    Continuous B ∧ (∀t,HasDerivAt B (r t) t) ∧ ∀ t≥a,B t-B a≤1/16 := by
  let B := fun t => ∫u in T..t, r u
  let J := ∫u in Ioi T, r u
  have d (t : ℝ) : HasDerivAt B (r t) t :=
    intervalIntegral.integral_hasDerivAt_right (cr.intervalIntegrable ..)
      cr.stronglyMeasurable.stronglyMeasurableAtFilter cr.continuousAt
  have cv : Tendsto B atTop (𝓝 J) := intervalIntegral_tendsto_integral_Ioi T ir tendsto_id
  obtain ⟨M,hM⟩ := eventually_atTop.mp (cv (Ioo_mem_nhds (show J-1/32<J by linarith) (show J<J+1/32 by linarith)))
  let a := max (max T 0) M+1
  have Ma : M≤a := by dsimp [a]; linarith [le_max_right (max T 0) M]
  refine ⟨a,?_,?_,B,continuous_iff_continuousAt.mpr (fun t => (d t).continuousAt),d,?_⟩
  · dsimp [a]; linarith [le_max_left (max T 0) M,le_max_right T 0]
  · dsimp [a]; linarith [le_max_left (max T 0) M,le_max_left T 0]
  · intro t ht
    linarith only [(hM t (Ma.trans ht)).2,(hM a Ma).1]

end LengthGrowth.ActualFlow.TurningEnvelope
#print axioms LengthGrowth.ActualFlow.TurningEnvelope.small_tail_budget
