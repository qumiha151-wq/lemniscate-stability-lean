import LengthGrowth.ExplicitWindow
import LengthGrowth.OscillatorExistence
import LengthGrowth.OscillatorMeanFloor
import LengthGrowth.OscillatorSmooth
import LengthGrowth.ActualFlow.CriticalRMSWindow

/-! An explicit uniform cubic-moment threshold for the closed planar
free elastic flow, derived from the actual material curvature integrals. -/
noncomputable section
open Filter
namespace LengthGrowth.ActualFlow.ExplicitCubicThreshold
open ExplicitWindow

theorem actual_window_comparison : PeriodicWindowGap.OscillatorWindowComparison m T (τ^2/T) := by
  apply from_exact_oscillators
  · intro x b v
    exact OscillatorSmooth.exists_smooth_at OscillatorMean.exists_global_c2_from_data x b v
  · intro z hz eqn B hB bound x
    exact OscillatorMean.global_c2_explicit_window_lower z (hz.of_le (by decide))
      eqn hB bound x T (by linarith only [T_large])

/-- Every smooth periodic regular material position satisfies the explicit spatial estimate. -/
theorem static_gap : StrictHalfSliceGap ε :=
  strictHalfSliceGap_of_oscillatorWindowComparison m_pos m_le_one
    (by linarith only [T_large]) tau_pos actual_window_comparison

/-- Explicit threshold in terms of elementary constants and the exponential. -/
def threshold : ℝ := 1/2-ε

theorem threshold_range : 0<threshold ∧ threshold<1/2 := by
  unfold threshold
  constructor <;> linarith only [eps_pos,eps_lt_half]

/-- A late lower bound for the actual cubic ratio gives both rates with no
additional assumptions on scaled bending energy or curvature sign. -/
theorem quarter_bounds_of_eventual (c : ForwardImmersion) (hf : c.IsNormalFEF)
    (h : ∀ᶠ t : ℝ in atTop, threshold < |c.signedCubicRatio t|) :
    c.HasQuarterLengthBound ∧ c.HasQuarterEnergyBound :=
  c.quarter_bounds_of_strict_half_tail hf eps_pos static_gap h

theorem quarter_bounds_of_liminf (c : ForwardImmersion) (hf : c.IsNormalFEF)
    (h : (threshold : EReal) <
      liminf (fun t : ℝ => ((|c.signedCubicRatio t| : ℝ) : EReal)) atTop) :
    c.HasQuarterLengthBound ∧ c.HasQuarterEnergyBound :=
  c.quarter_bounds_of_strict_half_liminf hf eps_pos static_gap h

/-- This bound on zero-turn trajectories holds without an energy cap
or an eventual lower bound for the cubic moment. -/
theorem zero_turn_liminf (c : ForwardImmersion) (hf : c.IsNormalFEF)
    (hzero : materialSignedCurvature (c.position 0) c.period=0) :
    liminf (fun t : ℝ => ((|c.signedCubicRatio t| : ℝ) : EReal)) atTop ≤ (threshold : EReal) :=
  c.zero_turn_liminf_le_strict_half hf eps_pos static_gap hzero

end LengthGrowth.ActualFlow.ExplicitCubicThreshold

open Lean Elab Command in
run_cmd do
  let names := #[`LengthGrowth.ActualFlow.ExplicitCubicThreshold.actual_window_comparison,
    `LengthGrowth.ActualFlow.ExplicitCubicThreshold.static_gap,
    `LengthGrowth.ActualFlow.ExplicitCubicThreshold.threshold_range,
    `LengthGrowth.ActualFlow.ExplicitCubicThreshold.quarter_bounds_of_eventual,
    `LengthGrowth.ActualFlow.ExplicitCubicThreshold.quarter_bounds_of_liminf,
    `LengthGrowth.ActualFlow.ExplicitCubicThreshold.zero_turn_liminf]
  for name in names do
    for ax in (← collectAxioms name) do
      unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
  logInfo "Explicit cubic threshold and consequences: six public theorems; standard axioms only."
