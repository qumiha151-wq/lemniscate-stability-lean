import LengthGrowth.ActualFlow.ArclengthSmooth
import LengthGrowth.ActualFlow.ArclengthTransport
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! The constructed global arclength inverse supplies every premise of the
transport lemmas. The actual substitution formula identifies the legacy
closed-curve integrals with the original material integrals.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace LengthGrowth.ActualFlow

def materialAbsoluteCurvature (γ : ℝ → ℂ) (P : ℝ) : ℝ :=
  ∫ u in 0..P, |curvature γ u| * speed γ u

namespace PeriodicRegularPosition

variable (c : PeriodicRegularPosition)

theorem unitSpeedPosition_speed (s : ℝ) : speed c.unitSpeedPosition s = 1 :=
  c.unitSpeedPosition_unit_speed s

theorem unitSpeedPosition_curvature (s : ℝ) :
    curvature c.unitSpeedPosition s = curvature c.position (c.arclengthInverse s) :=
  inverse_comp_curvature c.smooth c.regular c.inverse_smooth c.inverse_hasDerivAt s

theorem unitSpeedPosition_force (s : ℝ) :
    force c.unitSpeedPosition s = force c.position (c.arclengthInverse s) :=
  inverse_comp_force c.smooth c.regular c.inverse_smooth c.inverse_hasDerivAt s

theorem integral_comp_inverse {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ s in 0..c.length, f (c.arclengthInverse s)) =
      ∫ u in 0..c.period, f u * speed c.position u := by
  have h := intervalIntegral.integral_comp_mul_deriv
    (a := 0) (b := c.period) (f := c.arclength) (f' := speed c.position)
    (g := fun s => f (c.arclengthInverse s))
    (fun u _ => c.arclength_hasDerivAt u)
    (speed_smooth c.smooth c.regular).continuous.continuousOn
    (hf.comp c.inverse_continuous)
  simpa only [Function.comp_apply, c.arclength_inverse_right,
    c.arclength_zero, c.arclength_length] using h.symm

def closedFrenetCurve : LengthGrowth.ClosedFrenetCurve :=
  LengthGrowth.closedFrenetCurveOfPosition c.unitSpeedPosition c.length c.length_pos
    c.unitSpeedPosition_periodic c.unitSpeedPosition_smooth c.unitSpeedPosition_unit_speed

theorem closedFrenetCurve_period : c.closedFrenetCurve.period = c.length := rfl

theorem closedFrenetCurve_curvature (s : ℝ) :
    c.closedFrenetCurve.curvature s = curvature c.position (c.arclengthInverse s) := by
  change LengthGrowth.positionCurvature c.unitSpeedPosition s = _
  rw [legacy_curvature_eq_actual c.unitSpeedPosition_unit_speed,
    c.unitSpeedPosition_curvature]

theorem closedFrenetCurve_force (s : ℝ) :
    c.closedFrenetCurve.force s = force c.position (c.arclengthInverse s) := by
  change deriv (deriv (LengthGrowth.positionCurvature c.unitSpeedPosition)) s +
    LengthGrowth.positionCurvature c.unitSpeedPosition s ^ 3 / 2 = _
  rw [legacy_force_eq_actual c.unitSpeedPosition_unit_speed, c.unitSpeedPosition_force]

theorem closedFrenetCurve_energy :
    c.closedFrenetCurve.energy = materialEnergy c.position c.period := by
  unfold LengthGrowth.ClosedFrenetCurve.energy
  simp_rw [c.closedFrenetCurve_curvature]
  rw [c.closedFrenetCurve_period]
  have hi := c.integral_comp_inverse (f := fun u => curvature c.position u ^ 2)
    ((curvature_smooth c.smooth c.regular).continuous.pow 2)
  rw [hi]
  unfold materialEnergy
  ring

theorem closedFrenetCurve_dissipation :
    c.closedFrenetCurve.dissipation = materialDissipation c.position c.period := by
  unfold LengthGrowth.ClosedFrenetCurve.dissipation
  simp_rw [c.closedFrenetCurve_force]
  exact c.integral_comp_inverse ((force_smooth c.smooth c.regular).continuous.pow 2)

theorem closedFrenetCurve_absoluteCurvature :
    c.closedFrenetCurve.absoluteCurvature = materialAbsoluteCurvature c.position c.period := by
  unfold LengthGrowth.ClosedFrenetCurve.absoluteCurvature
  simp_rw [c.closedFrenetCurve_curvature]
  exact c.integral_comp_inverse (curvature_smooth c.smooth c.regular).continuous.abs

end PeriodicRegularPosition
end LengthGrowth.ActualFlow

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (n, _) in (← getEnv).constants do
    if (`LengthGrowth).isPrefixOf n then
      for a in (← collectAxioms n) do
        unless allowed.contains a do throwError "Unexpected axiom {a} in {n}"
      count := count + 1
  logInfo m!"Actual arclength integral transport: {count} declarations, standard axioms only."
