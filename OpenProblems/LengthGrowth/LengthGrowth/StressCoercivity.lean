import LengthGrowth.StressClosureBounds
import LengthGrowth.StressNormVariation
import LengthGrowth.StressNormalization
import LengthGrowth.StressClosingAlgebra

/-!
# Coercivity of the actual elastic force on a closed planar curve

All geometric and integral hypotheses of the stress argument are now
discharged for `ClosedFrenetCurve`. In particular, no stress lower bound,
direction cone, energy estimate, or nonzero-force assumption is supplied
to the final theorem.
-/

noncomputable section
open Set
namespace LengthGrowth.ClosedFrenetCurve

variable (c : LengthGrowth.ClosedFrenetCurve)

theorem curvature_peak_ratio_gt {s₀ : ℝ} (hs₀ : s₀ ∈ Icc 0 c.period)
    (hpeakpos : 0 < |c.curvature s₀|) (hk₁ : c.curvature₁ s₀ = 0)
    (hmax : ∀ s, |c.curvature s| ≤ |c.curvature s₀|) :
    (1:ℝ)/4096 < Real.sqrt (c.energy*c.dissipation)/|c.curvature s₀|^3 := by
  let M := |c.curvature s₀|
  let B := Real.sqrt c.curvatureGradientSquare
  have hM : 0 < M := hpeakpos
  have hE := c.energy_pos
  have hD := c.dissipation_nonneg
  change (1:ℝ)/4096 < Real.sqrt (c.energy*c.dissipation)/M^3
  by_contra hn
  have hr : Real.sqrt (c.energy*c.dissipation)/M^3 ≤ 1/4096 := le_of_not_gt hn
  have hr0 : 0 ≤ Real.sqrt (c.energy*c.dissipation)/M^3 := by positivity
  have hpoint : M^2 ≤ 4*c.energy^2+2*Real.sqrt (2*c.energy)*B := by
    simpa only [M, B, sq_abs] using c.curvature_pointwise_bound hs₀
  have hgradient : B^2 ≤ c.energy*M^2+Real.sqrt (2*c.energy*c.dissipation) := by
    dsimp [B]
    rw [Real.sq_sqrt c.curvature_gradient_nonneg]
    exact c.curvature_gradient_bound hM.le (fun s _ => hmax s)
  have hquad := StressAlgebra.normalized_pointwise_bound hE hM hD
    (Real.sqrt_nonneg _) hpoint hgradient
  have hx : M/c.energy < 64 := StressAlgebra.ratio_lt64
    (by positivity) hr0 (hr.trans (by norm_num)) hquad
  have hB := StressAlgebra.curvature_derivative_bound hE hM hgradient hr hx
  have hvariation := StressAlgebra.stress_variation_normalized hE.le hM hD hB
  have hnorm (s : ℝ) : M^2/4 ≤ ‖c.stress s‖ ∧ ‖c.stress s‖ ≤ M^2 := by
    have hactual := c.stress_norm_sq_variation_from_peak hs₀ hk₁ s
    change |‖c.stress s‖^2-M^4/4| ≤ 2*B*Real.sqrt c.dissipation at hactual
    exact StressAlgebra.stress_norm_bounds (norm_nonneg _) hM.le hr
      (hactual.trans hvariation)
  have hW : ∀ s, c.stress s ≠ 0 := by
    intro s
    apply norm_pos_iff.mp
    exact lt_of_lt_of_le (by positivity : 0 < M^2/4) (hnorm s).1
  have hroot : 8*Real.sqrt (2*c.energy*c.dissipation)/M^3 =
      8*Real.sqrt 2*(Real.sqrt (c.energy*c.dissipation)/M^3) := by
    rw [show 2*c.energy*c.dissipation=2*(c.energy*c.dissipation) by ring,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    ring
  have hunit := c.stressDirection_unit s₀ (hW s₀)
  have hcone (s : ℝ) (hs : s ∈ Icc 0 c.period) : (1:ℝ)/2 ≤
      ((starRingEnd ℂ) (c.stressDirection s₀)*c.stressDirection s).re := by
    have ho := c.stress_direction_oscillation hM (fun u _ => hmax u)
      (fun u => (hnorm u).1) hs hs₀
    rw [hroot] at ho
    exact unit_projection_lower hunit
      (ho.trans (StressAlgebra.unit_stress_variation_lt_half hr).le)
  have hlo := c.stress_integral_lower_bound hM hunit hW
    (fun s _ => (hnorm s).2) hcone
  have hhi := c.stress_integral_upper_bound hM (fun s => (hnorm s).1)
  have hclose := hlo.trans hhi
  have hfactor := StressAlgebra.normalized_closing_bound hE hM hD hclose
  exact (not_le_of_gt (StressAlgebra.closing_factor_lt_one hr0 hr hx)) hfactor

/-- The actual force of every closed unit-speed planar curve controls the
sixth power of curvature at every point. This is the sup-curvature stress
coercivity inequality, stated pointwise to avoid an extra supremum API. -/
theorem energy_dissipation_controls_curvature (s : ℝ) :
    (1/16777216:ℝ)*|c.curvature s|^6 ≤ c.energy*c.dissipation := by
  obtain ⟨s₀, hs₀, hpos, hk₁, hmax⟩ := c.exists_curvature_peak
  have hr := c.curvature_peak_ratio_gt hs₀ hpos hk₁ hmax
  have hmain := StressAlgebra.energy_dissipation_of_ratio
    c.energy_pos hpos c.dissipation_nonneg hr
  have hpow := pow_le_pow_left₀ (abs_nonneg (c.curvature s)) (hmax s) 6
  exact (mul_le_mul_of_nonneg_left hpow (by norm_num)).trans hmain

end LengthGrowth.ClosedFrenetCurve

#print axioms LengthGrowth.ClosedFrenetCurve.energy_dissipation_controls_curvature

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
  logInfo m!"LengthGrowth complete stress-coercivity audit passed for {checked} declarations."
