import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.UnitInterval

/-! The angle primitive has the correct initial right derivative even
when its measurable angular velocity was assigned a different value at zero. -/
noncomputable section
namespace Lemniscate
open MeasureTheory Filter Set
open scoped Topology

/-- Agreement with the continuous initial angular velocity on the positive
initial interval determines the right derivative of its actual integral. -/
theorem rotation_angle_initial_derivative
    (τ : ℝ) (hτ : 0 < τ) (ω : ℝ → ℝ) (W : C(unitInterval,ℝ))
    (hω : ∀ t : ℝ, 0 < t → t ≤ τ →
      ω t=W (Set.projIcc (0:ℝ) 1 zero_le_one (t/τ))) :
    HasDerivWithinAt (fun t : ℝ => ∫ s in (0:ℝ)..t, ω s)
      (W 0) (Ici (0:ℝ)) 0 := by
  let w : ℝ → ℝ := fun t => W (Set.projIcc (0:ℝ) 1 zero_le_one (t/τ))
  have hw : Continuous w := W.continuous.comp
    (continuous_projIcc.comp (continuous_id.div_const τ))
  let P : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, w s
  have hw0 : w 0=W 0 := by
    simp only [w,zero_div,Set.projIcc_left]
    exact congrArg W (Subtype.ext rfl)
  have hP : HasDerivAt P (W 0) 0 :=
    (intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable 0 0)
      hw.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt).congr_deriv hw0
  have heq (t : ℝ) (ht : 0 ≤ t) (htτ : t ≤ τ) :
      (∫ s in (0:ℝ)..t, ω s)=P t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with s hs
    rw [uIoc_of_le ht] at hs
    exact hω s hs.1 (hs.2.trans htτ)
  have hgerm : (fun t : ℝ => ∫ s in (0:ℝ)..t, ω s) =ᶠ[𝓝[Ici (0:ℝ)] 0] P := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hτ)] with t ht htτ
    exact heq t ht htτ.le
  have hwithin : HasDerivWithinAt P (W 0) (Ici (0:ℝ)) 0 := hP.hasDerivWithinAt
  exact hwithin.congr_of_eventuallyEq_of_mem hgerm (by simp)

end Lemniscate
