import LengthGrowth.StressCoercivity

/-! The total absolute curvature controls the actual elastic-force
coercivity constant. This is a static geometric theorem; it does not
assert bounded total absolute curvature along arbitrary flows. -/

noncomputable section
open MeasureTheory Set
namespace LengthGrowth.ClosedFrenetCurve

variable (c : LengthGrowth.ClosedFrenetCurve)

theorem energy_le_curvature_max_times_absoluteCurvature {M : ℝ} (_hM : 0 ≤ M)
    (hmax : ∀ s ∈ Icc 0 c.period, |c.curvature s| ≤ M) :
    2*c.energy ≤ M*c.absoluteCurvature := by
  have hp (s : ℝ) (hs : s ∈ Icc 0 c.period) : c.curvature s^2 ≤ M*|c.curvature s| := by
    have h := mul_le_mul_of_nonneg_right (hmax s hs) (abs_nonneg (c.curvature s))
    simpa only [← pow_two, sq_abs] using h
  have hi := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun s => c.curvature s^2) (g := fun s => M*|c.curvature s|)
    c.period_pos.le ((c.curvature_continuous.pow 2).intervalIntegrable _ _)
    ((c.curvature_continuous.abs.const_mul M).intervalIntegrable _ _) hp
  rw [intervalIntegral.integral_const_mul] at hi
  dsimp [energy, absoluteCurvature]
  linarith

theorem absolute_curvature_coercivity_scaled :
    c.energy^5 ≤ 262144*c.absoluteCurvature^6*c.dissipation := by
  obtain ⟨s₀, hs₀, hM, hk₁, hmax⟩ := c.exists_curvature_peak
  let M := |c.curvature s₀|
  have hEA := c.energy_le_curvature_max_times_absoluteCurvature hM.le
    (fun s _ => hmax s)
  have hmain := c.energy_dissipation_controls_curvature s₀
  have he := c.energy_pos
  have hpow := pow_le_pow_left₀ (show 0 ≤ 2*c.energy by positivity) hEA 6
  rw [mul_pow, mul_pow] at hpow
  norm_num at hpow
  have hmul := mul_le_mul_of_nonneg_right hmain (pow_nonneg
    (le_trans (by norm_num : (0:ℝ) ≤ 1) c.one_le_absoluteCurvature) 6)
  have hpre : c.energy*c.energy^5 ≤
      c.energy*(262144*c.absoluteCurvature^6*c.dissipation) := by
    nlinarith
  exact (mul_le_mul_iff_right₀ he).mp hpre

/-- An unconditional inequality for each actual closed curve. The
denominator is its actual total absolute curvature, which is positive
by the closing condition proved earlier. -/
theorem absolute_curvature_coercivity :
    (1/262144:ℝ)*c.energy^5/c.absoluteCurvature^6 ≤ c.dissipation := by
  have hA : 0 < c.absoluteCurvature :=
    lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) c.one_le_absoluteCurvature
  apply (div_le_iff₀ (pow_pos hA 6)).mpr
  have h := c.absolute_curvature_coercivity_scaled
  nlinarith

end LengthGrowth.ClosedFrenetCurve

#print axioms LengthGrowth.ClosedFrenetCurve.absolute_curvature_coercivity

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
  logInfo m!"LengthGrowth absolute-curvature coercivity audit passed for {checked} declarations."
