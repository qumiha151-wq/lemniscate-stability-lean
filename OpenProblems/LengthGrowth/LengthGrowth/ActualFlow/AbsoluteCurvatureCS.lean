import LengthGrowth.ActualFlow.ArclengthCoercivity

/-! Actual total-curvature Cauchy--Schwarz and a weak virial estimate.
These are static inequalities for arbitrary-speed closed immersions.
No time-uniform bound, normal-flow equation or geometric existence is assumed. -/

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth

namespace ClosedFrenetCurve

theorem absoluteCurvature_sq_le (c : ClosedFrenetCurve) :
    c.absoluteCurvature ^ 2 ≤ 2 * c.energy * c.period := by
  have h := interval_integral_mul_sq_le c.curvature_continuous.abs
    (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))) c.period_pos.le
  simp [sq_abs] at h
  dsimp [absoluteCurvature, energy]
  nlinarith

end ClosedFrenetCurve

namespace ActualFlow

namespace PeriodicRegularPosition

variable (c : PeriodicRegularPosition)

theorem material_absoluteCurvature_sq_le :
    materialAbsoluteCurvature c.position c.period ^ 2 ≤
      2 * materialEnergy c.position c.period * materialLength c.position c.period := by
  simpa only [c.closedFrenetCurve_absoluteCurvature, c.closedFrenetCurve_energy,
    c.closedFrenetCurve_period, length] using c.closedFrenetCurve.absoluteCurvature_sq_le

/-- A deliberately non-sharp constant, obtained entirely within this project. -/
theorem material_weak_virial :
    (1 / 2097152 : ℝ) * materialEnergy c.position c.period ^ 2 /
      materialLength c.position c.period ^ 3 ≤ materialDissipation c.position c.period := by
  let E := materialEnergy c.position c.period
  let L := materialLength c.position c.period
  let A := materialAbsoluteCurvature c.position c.period
  let D := materialDissipation c.position c.period
  have hE : 0 < E := c.material_energy_pos
  have hL : 0 < L := c.length_pos
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) c.material_absolute_curvature_lower
  have hcs : A ^ 2 ≤ 2 * E * L := c.material_absoluteCurvature_sq_le
  have hcube := pow_le_pow_left₀ (sq_nonneg A) hcs 3
  have hden : A ^ 6 ≤ 8 * E ^ 3 * L ^ 3 := by nlinarith [hcube]
  have hq := div_le_div_of_nonneg_left
    (show 0 ≤ (1 / 262144 : ℝ) * E ^ 5 by positivity) (pow_pos hA 6) hden
  have hfinal := hq.trans c.material_absolute_curvature_coercivity
  change (1 / 2097152 : ℝ) * E ^ 2 / L ^ 3 ≤ D
  convert! hfinal using 1
  field_simp [ne_of_gt hE, ne_of_gt hL]
  ring

end PeriodicRegularPosition

namespace ForwardImmersion

variable (c : ForwardImmersion)

theorem length_pos {t : ℝ} (ht : 0 ≤ t) : 0 < c.length t :=
  (c.regularPositionAt ht).length_pos

theorem absoluteCurvature_sq_le {t : ℝ} (ht : 0 ≤ t) :
    c.absoluteCurvature t ^ 2 ≤ 2 * c.energy t * c.length t :=
  (c.regularPositionAt ht).material_absoluteCurvature_sq_le

theorem weak_virial {t : ℝ} (ht : 0 ≤ t) :
    (1 / 2097152 : ℝ) * c.energy t ^ 2 / c.length t ^ 3 ≤ c.dissipation t :=
  (c.regularPositionAt ht).material_weak_virial

end ForwardImmersion
end ActualFlow
end LengthGrowth

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (n, _) in (← getEnv).constants do
    if (`LengthGrowth).isPrefixOf n || (`FreeElasticScalar).isPrefixOf n then
      for a in (← collectAxioms n) do
        unless allowed.contains a do throwError "Unexpected axiom {a} in {n}"
      count := count + 1
  logInfo m!"Actual curvature CS and weak virial: {count} declarations; standard axioms only."
