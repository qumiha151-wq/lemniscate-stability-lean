import LengthGrowth.ActualFlow.CriticalRMSAdapter
import LengthGrowth.PeriodicWindowGap

/-! Specialization of the arclength RMS transfer to the periodic window theorem. -/
noncomputable section
namespace LengthGrowth.ActualFlow
open PeriodicWindowGap

theorem strictHalfSliceGap_of_oscillatorWindowComparison {m T τ : ℝ}
    (hm : 0<m) (hm1 : m≤1) (hT : 0<T) (hτ : 0<τ)
    (cmp : OscillatorWindowComparison m T (τ^2/T)) :
    StrictHalfSliceGap (gapEpsilon m T τ) := by
  apply strictHalfSliceGap_of_scalar
  intro P u hP hu hp
  dsimp only
  intro hu2 hs he
  exact scalar_strict_half_gap hm hm1 hT hτ cmp hP hu hp hu2 hs he

#print axioms strictHalfSliceGap_of_oscillatorWindowComparison
end LengthGrowth.ActualFlow
