import LengthGrowth.ActualFlow.MaterialTurnFlux
import LengthGrowth.ActualFlow.TurningQuarterFlow
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open Set MeasureTheory Function
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow

namespace PeriodicRegularPosition
variable (p : PeriodicRegularPosition)

theorem arcTurn_between_primitives (a b : ℝ) :
    arcTurn p.position 0 b-arcTurn p.position 0 a=arcTurn p.position a b := by
  have ct := (curvature_smooth p.smooth p.regular).continuous.mul (speed_smooth p.smooth p.regular).continuous
  have h := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (ct.intervalIntegrable 0 a) (ct.intervalIntegrable a b)
  simp only [Pi.mul_apply] at h
  unfold arcTurn
  linarith

theorem arcTurn_periodic_increment (h : ℝ) :
    Periodic (fun x => arcTurn p.position 0 (x+h)-arcTurn p.position 0 x) p.period := by
  intro x
  dsimp only
  rw [p.arcTurn_between_primitives,p.arcTurn_between_primitives]
  let f := fun v => curvature p.position v*speed p.position v
  have per : Periodic f p.period := (curvature_periodic p.smooth p.regular p.periodic).mul
    (speed_periodic p.smooth p.periodic)
  change (∫v in x+p.period..(x+p.period)+h,f v)=(∫v in x..x+h,f v)
  rw [show x+p.period+h=x+h+p.period by ring,←intervalIntegral.integral_comp_add_right]
  exact intervalIntegral.integral_congr fun v _ => per v

theorem arcTurn_scaled (s a b : ℝ) :
    (∫u in a..b,p.scaledArclengthCurvature s u)=
      arcTurn p.position (p.arclengthInverse (s*a)) (p.arclengthInverse (s*b)) := by
  rw [p.turning_on_scaled_interval]
  let l := p.arclengthInverse (s*a)
  let r := p.arclengthInverse (s*b)
  have changeVar := intervalIntegral.integral_comp_mul_deriv (a:=l) (b:=r)
    (f:=p.arclength) (f':=speed p.position) (g:=p.closedFrenetCurve.curvature)
    (fun u _ => p.arclength_hasDerivAt u) (speed_smooth p.smooth p.regular).continuous.continuousOn
    p.closedFrenetCurve.curvature_continuous
  rw [show p.arclength l=s*a from p.arclength_inverse_left _,show p.arclength r=s*b from p.arclength_inverse_left _] at changeVar
  rw [←changeVar]
  apply intervalIntegral.integral_congr
  intro u _
  change p.closedFrenetCurve.curvature (p.arclength u)*speed p.position u=_
  rw [p.closedFrenetCurve_curvature,p.arclength_inverse_right]
end PeriodicRegularPosition

end LengthGrowth.ActualFlow
#print axioms LengthGrowth.ActualFlow.PeriodicRegularPosition.arcTurn_scaled
