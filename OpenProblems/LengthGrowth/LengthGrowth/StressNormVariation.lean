import LengthGrowth.CurvaturePeak

/-! Norm variation of the actual elastic stress, obtained by integrating
its true derivative and applying the proved interval Cauchy--Schwarz. -/
noncomputable section
open MeasureTheory Set
namespace LengthGrowth.ClosedFrenetCurve

variable (c : LengthGrowth.ClosedFrenetCurve)

theorem stress_norm_sq_oscillation {s t : ℝ}
    (hs : s ∈ Icc 0 c.period) (ht : t ∈ Icc 0 c.period) :
    |‖c.stress s‖^2-‖c.stress t‖^2| ≤
      2*Real.sqrt c.curvatureGradientSquare*Real.sqrt c.dissipation := by
  have ho := LengthGrowth.interval_oscillation_le c.stress_norm_sq_deriv
    ((c.curvature₁_continuous.const_mul 2).mul c.force_continuous) hs ht
  change |‖c.stress s‖^2-‖c.stress t‖^2| ≤
    ∫ u in 0..c.period, |2*c.curvature₁ u*c.force u| at ho
  have hcs := LengthGrowth.interval_integral_abs_mul_le
    c.curvature₁_continuous c.force_continuous c.period_pos.le
  change (∫ u in 0..c.period, |c.curvature₁ u*c.force u|) ≤
    Real.sqrt c.curvatureGradientSquare*Real.sqrt c.dissipation at hcs
  have hi : (∫ u in 0..c.period, |2*c.curvature₁ u*c.force u|) =
      2*(∫ u in 0..c.period, |c.curvature₁ u*c.force u|) := by
    rw [show (fun u => |2*c.curvature₁ u*c.force u|) =
        (fun u => 2*|c.curvature₁ u*c.force u|) by
      funext u
      rw [mul_assoc, abs_mul]
      norm_num]
    exact intervalIntegral.integral_const_mul _ _
  rw [hi] at ho
  linarith

theorem stress_norm_sq_variation_from_peak {s₀ : ℝ}
    (hs₀ : s₀ ∈ Icc 0 c.period) (hk₁ : c.curvature₁ s₀ = 0) (s : ℝ) :
    |‖c.stress s‖^2-|c.curvature s₀|^4/4| ≤
      2*Real.sqrt c.curvatureGradientSquare*Real.sqrt c.dissipation := by
  obtain ⟨u, hu, heq⟩ := c.periodic_representative c.stress_periodic s
  have ho := c.stress_norm_sq_oscillation hu hs₀
  rw [heq, c.stress_norm_sq s₀, hk₁] at ho
  simpa only [zero_pow (by decide : (2:ℕ) ≠ 0), zero_add,
    show |c.curvature s₀|^4=c.curvature s₀^4 from
      (show Even (4:ℕ) by decide).pow_abs _] using ho

end LengthGrowth.ClosedFrenetCurve

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`LengthGrowth).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"LengthGrowth stress-norm variation audit passed for {checked} declarations."
