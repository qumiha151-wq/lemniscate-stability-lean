import LengthGrowth.ActualFlow.MaterialIntegrals
import LengthGrowth.ActualFlow.SpatialPeriodicity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Order.Hom.Set

/-! The global arclength coordinate is constructed from actual position data.
Its inverse is obtained from proved strict monotonicity and surjectivity;
there is no supplied reparametrization or unit-speed hypothesis. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace LengthGrowth.ActualFlow

structure PeriodicRegularPosition where
  period : ℝ
  period_pos : 0 < period
  position : ℝ → ℂ
  smooth : ContDiff ℝ ∞ position
  periodic : Function.Periodic position period
  regular : ∀ u, deriv position u ≠ 0

namespace PeriodicRegularPosition

variable (c : PeriodicRegularPosition)

def length : ℝ := materialLength c.position c.period

def arclength (u : ℝ) : ℝ := ∫ v in 0..u, speed c.position v

theorem arclength_zero : c.arclength 0 = 0 := by simp [arclength]

theorem arclength_length : c.arclength c.period = c.length := rfl

theorem arclength_hasDerivAt (u : ℝ) :
    HasDerivAt c.arclength (speed c.position u) u := by
  have hg := (speed_smooth c.smooth c.regular).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
    hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt

theorem arclength_deriv : deriv c.arclength = speed c.position :=
  funext fun u => (c.arclength_hasDerivAt u).deriv

theorem arclength_smooth : ContDiff ℝ ∞ c.arclength := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun u => (c.arclength_hasDerivAt u).differentiableAt, ?_⟩
  rw [c.arclength_deriv]
  exact speed_smooth c.smooth c.regular

theorem length_pos : 0 < c.length := by
  apply intervalIntegral.integral_pos c.period_pos
    (speed_smooth c.smooth c.regular).continuous.continuousOn
  · exact fun u _ => (speed_pos c.regular u).le
  · exact ⟨0, ⟨le_rfl, c.period_pos.le⟩, speed_pos c.regular 0⟩

theorem arclength_add_period (u : ℝ) :
    c.arclength (u + c.period) = c.arclength u + c.length := by
  have hp := speed_periodic c.smooth c.periodic
  have hg := (speed_smooth c.smooth c.regular).continuous
  simpa only [arclength, length, materialLength, zero_add] using
    hp.intervalIntegral_add_eq_add 0 u (fun a b => hg.intervalIntegrable a b)

theorem arclength_strictMono : StrictMono c.arclength := by
  apply strictMono_of_deriv_pos
  intro u
  rw [c.arclength_deriv]
  exact speed_pos c.regular u

/-- The difference from a positive linear map is genuinely periodic. -/
theorem arclength_linear_error_periodic : Function.Periodic
    (fun u => c.arclength u - (c.length / c.period) * u) c.period := by
  intro u
  dsimp only
  have hp : c.period ≠ 0 := ne_of_gt c.period_pos
  rw [c.arclength_add_period, mul_add, div_mul_cancel₀ c.length hp]
  ring

theorem arclength_surjective : Function.Surjective c.arclength := by
  have ha : 0 < c.length / c.period := div_pos c.length_pos c.period_pos
  have hc : Continuous (fun u => c.arclength u - (c.length / c.period) * u) :=
    c.arclength_smooth.continuous.sub (continuous_const.mul continuous_id)
  obtain ⟨M, _, hb⟩ := (c.arclength_linear_error_periodic.isBounded_of_continuous
    (ne_of_gt c.period_pos) hc).exists_pos_norm_le
  have hbounds (u : ℝ) : -M ≤ c.arclength u - (c.length / c.period) * u ∧
      c.arclength u - (c.length / c.period) * u ≤ M := by
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using (hb _ (mem_range_self u)))
  apply c.arclength_smooth.continuous.surjective
  · apply tendsto_atTop_atTop.mpr
    intro b
    refine ⟨(b + M) / (c.length / c.period), ?_⟩
    intro u hu
    have hmul := (div_le_iff₀ ha).mp hu
    have hb := (hbounds u).1
    nlinarith
  · apply tendsto_atBot_atBot.mpr
    intro b
    refine ⟨(b - M) / (c.length / c.period), ?_⟩
    intro u hu
    have hmul := (le_div_iff₀ ha).mp hu
    have hb := (hbounds u).2
    nlinarith

def arclengthOrderIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective c.arclength c.arclength_strictMono
    c.arclength_surjective

def arclengthInverse (s : ℝ) : ℝ := c.arclengthOrderIso.symm s

def unitSpeedPosition (s : ℝ) : ℂ := c.position (c.arclengthInverse s)

theorem arclength_inverse_left (s : ℝ) :
    c.arclength (c.arclengthInverse s) = s :=
  c.arclengthOrderIso.apply_symm_apply s

theorem arclength_inverse_right (u : ℝ) :
    c.arclengthInverse (c.arclength u) = u :=
  c.arclengthOrderIso.symm_apply_apply u

theorem inverse_zero : c.arclengthInverse 0 = 0 := by
  simpa only [c.arclength_zero] using c.arclength_inverse_right 0

theorem inverse_length : c.arclengthInverse c.length = c.period := by
  simpa only [c.arclength_length] using c.arclength_inverse_right c.period

theorem inverse_add_length (s : ℝ) :
    c.arclengthInverse (s + c.length) = c.arclengthInverse s + c.period := by
  apply c.arclength_strictMono.injective
  rw [c.arclength_inverse_left, c.arclength_add_period, c.arclength_inverse_left]

theorem inverse_continuous : Continuous c.arclengthInverse :=
  c.arclengthOrderIso.toHomeomorph.symm.continuous

end PeriodicRegularPosition
end LengthGrowth.ActualFlow

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`LengthGrowth.ActualFlow).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext, `Classical.choice, `Quot.sound] : Array Name).contains axiomName do
          throwError "Arclength coordinate audit failed: {name} depends on {axiomName}"
      count := count + 1
  logInfo m!"ACTUAL_ARCLENGTH_COORDINATE_AUDIT {count}: standard three axioms only."
