import LengthGrowth.StressDirection

/-! Integrating the actual unit-stress velocity, preserving its curvature
weight. The stress lower bound is a local intermediate hypothesis; the
full contradiction theorem derives it from actual energy/dissipation. -/

noncomputable section
open MeasureTheory Set
namespace LengthGrowth.ClosedFrenetCurve

variable (c : LengthGrowth.ClosedFrenetCurve)

theorem absolute_curvature_force_integral_bound :
    (∫ s in 0..c.period, |c.curvature s*c.force s|) ≤
      Real.sqrt (2*c.energy*c.dissipation) := by
  have h := LengthGrowth.interval_integral_abs_mul_le
    c.curvature_continuous c.force_continuous c.period_pos.le
  have he : (∫ s in 0..c.period, c.curvature s^2)=2*c.energy := by
    dsimp [energy]
    ring
  rw [he] at h
  rw [Real.sqrt_mul (mul_nonneg (by norm_num) c.energy_pos.le)]
  exact h

theorem weighted_force_integral_bound {M : ℝ} (hM : 0 ≤ M)
    (hmax : ∀ s ∈ Icc 0 c.period, |c.curvature s| ≤ M) :
    (∫ s in 0..c.period, c.curvature s^2*|c.force s|) ≤
      M*Real.sqrt (2*c.energy*c.dissipation) := by
  have hk := c.curvature_continuous
  have hF := c.force_continuous
  calc
    _ ≤ ∫ s in 0..c.period, M*|c.curvature s*c.force s| := by
      apply intervalIntegral.integral_mono_on
        (f := fun s => c.curvature s^2*|c.force s|)
        (g := fun s => M*|c.curvature s*c.force s|) c.period_pos.le
        (((hk.pow 2).mul hF.abs).intervalIntegrable _ _)
        (((hk.mul hF).abs.const_mul M).intervalIntegrable _ _)
      intro s hs
      rw [abs_mul]
      have h := mul_le_mul_of_nonneg_right (hmax s hs)
        (mul_nonneg (abs_nonneg (c.curvature s)) (abs_nonneg (c.force s)))
      rw [← mul_assoc, ← pow_two, sq_abs] at h
      simpa only [mul_assoc] using h
    _ = M*(∫ s in 0..c.period, |c.curvature s*c.force s|) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left c.absolute_curvature_force_integral_bound hM

theorem stressDirectionDerivative_continuous (hW : ∀ s, c.stress s ≠ 0) :
    Continuous c.stressDirectionDerivative := by
  have hd : ∀ s, 2*‖c.stress s‖^3 ≠ 0 := fun s =>
    mul_ne_zero (by norm_num) (pow_ne_zero 3 (norm_ne_zero_iff.mpr (hW s)))
  have hc := (c.force_continuous.mul (c.curvature_continuous.pow 2)).div
    (continuous_const.mul (c.stress_continuous.norm.pow 3)) hd
  exact (Complex.continuous_ofReal.comp hc).mul
    (continuous_const.mul c.stress_continuous)

theorem stress_direction_oscillation {M s t : ℝ} (hM : 0 < M)
    (hmax : ∀ u ∈ Icc 0 c.period, |c.curvature u| ≤ M)
    (hlower : ∀ u, M^2/4 ≤ ‖c.stress u‖)
    (hs : s ∈ Icc 0 c.period) (ht : t ∈ Icc 0 c.period) :
    ‖c.stressDirection s-c.stressDirection t‖ ≤
      8*Real.sqrt (2*c.energy*c.dissipation)/M^3 := by
  have hW : ∀ u, c.stress u ≠ 0 := by
    intro u
    apply norm_pos_iff.mp
    exact lt_of_lt_of_le (by positivity : 0 < M^2/4) (hlower u)
  have ho := LengthGrowth.interval_oscillation_le
    (fun u => c.stressDirection_deriv u (hW u))
    (c.stressDirectionDerivative_continuous hW) hs ht
  have hpoint (u : ℝ) : ‖c.stressDirectionDerivative u‖ ≤
      (8/M^4)*(c.curvature u^2*|c.force u|) := by
    rw [c.stressDirectionDerivative_norm u (hW u)]
    have hsq : (M^2/4)^2 ≤ ‖c.stress u‖^2 :=
      (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr (hlower u)
    calc
      _ ≤ (c.curvature u^2*|c.force u|)/(2*(M^2/4)^2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left hsq (by norm_num))
      _ = _ := by field_simp; ring
  have hi : (∫ u in 0..c.period, ‖c.stressDirectionDerivative u‖) ≤
      (8/M^4)*(∫ u in 0..c.period, c.curvature u^2*|c.force u|) := by
    calc
      _ ≤ ∫ u in 0..c.period, (8/M^4)*(c.curvature u^2*|c.force u|) := by
        apply intervalIntegral.integral_mono_on c.period_pos.le
          ((c.stressDirectionDerivative_continuous hW).norm.intervalIntegrable _ _)
          ((((c.curvature_continuous.pow 2).mul c.force_continuous.abs).const_mul
            (8/M^4)).intervalIntegrable _ _)
        intro u _
        exact hpoint u
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hw := mul_le_mul_of_nonneg_left (c.weighted_force_integral_bound hM.le hmax)
    (show 0 ≤ 8/M^4 by positivity)
  have hend : (8/M^4)*(M*Real.sqrt (2*c.energy*c.dissipation)) =
      8*Real.sqrt (2*c.energy*c.dissipation)/M^3 := by
    field_simp
  exact (ho.trans hi).trans (hw.trans_eq hend)

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
  logInfo m!"LengthGrowth stress-direction bounds audit passed for {checked} declarations."
