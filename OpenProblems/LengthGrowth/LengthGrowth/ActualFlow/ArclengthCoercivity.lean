import LengthGrowth.ActualFlow.ArclengthIntegrals
import LengthGrowth.ActualFlow.ForwardGeometry

/-! Static coercivity for an actual arbitrary-speed periodic immersion, and
for the genuine material quantities of each time slice. These inequalities
do not assume a normal velocity equation or a time-uniform curvature bound.
-/

noncomputable section
open Set
open scoped ContDiff

namespace LengthGrowth.ActualFlow

namespace PeriodicRegularPosition

variable (c : PeriodicRegularPosition)

theorem material_stress_coercivity (u : ℝ) :
    (1 / 16777216 : ℝ) * |curvature c.position u| ^ 6 ≤
      materialEnergy c.position c.period * materialDissipation c.position c.period := by
  have h := c.closedFrenetCurve.energy_dissipation_controls_curvature (c.arclength u)
  simpa only [c.closedFrenetCurve_curvature, c.arclength_inverse_right,
    c.closedFrenetCurve_energy, c.closedFrenetCurve_dissipation] using h

theorem material_absolute_curvature_coercivity :
    (1 / 262144 : ℝ) * (materialEnergy c.position c.period) ^ 5 /
      (materialAbsoluteCurvature c.position c.period) ^ 6 ≤
      materialDissipation c.position c.period := by
  simpa only [c.closedFrenetCurve_energy, c.closedFrenetCurve_dissipation,
    c.closedFrenetCurve_absoluteCurvature] using c.closedFrenetCurve.absolute_curvature_coercivity

theorem material_energy_pos : 0 < materialEnergy c.position c.period := by
  simpa only [c.closedFrenetCurve_energy] using c.closedFrenetCurve.energy_pos

theorem material_absolute_curvature_lower :
    1 ≤ materialAbsoluteCurvature c.position c.period := by
  simpa only [c.closedFrenetCurve_absoluteCurvature] using
    c.closedFrenetCurve.one_le_absoluteCurvature

end PeriodicRegularPosition

namespace SmoothPeriodicImmersion

variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

def regularPositionAt {t : ℝ} (ht : t ∈ I) : PeriodicRegularPosition where
  period := c.period
  period_pos := c.period_pos
  position := c.position t
  smooth := c.position_slice_smooth ht
  periodic := c.periodic t ht
  regular := c.immersion t ht

def absoluteCurvature (t : ℝ) : ℝ := materialAbsoluteCurvature (c.position t) c.period

theorem energy_pos {t : ℝ} (ht : t ∈ I) : 0 < c.energy t :=
  (c.regularPositionAt ht).material_energy_pos

theorem absoluteCurvature_lower {t : ℝ} (ht : t ∈ I) : 1 ≤ c.absoluteCurvature t :=
  (c.regularPositionAt ht).material_absolute_curvature_lower

theorem stress_coercivity {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    (1 / 16777216 : ℝ) * |curvature (c.position t) u| ^ 6 ≤
      c.energy t * c.dissipation t :=
  (c.regularPositionAt ht).material_stress_coercivity u

theorem absolute_curvature_coercivity {t : ℝ} (ht : t ∈ I) :
    (1 / 262144 : ℝ) * c.energy t ^ 5 / c.absoluteCurvature t ^ 6 ≤ c.dissipation t :=
  (c.regularPositionAt ht).material_absolute_curvature_coercivity

end SmoothPeriodicImmersion

namespace ForwardImmersion

variable (c : ForwardImmersion)

def regularPositionAt {t : ℝ} (ht : 0 ≤ t) : PeriodicRegularPosition where
  period := c.period
  period_pos := c.period_pos
  position := c.position t
  smooth := c.position_slice_smooth ht
  periodic := c.periodic t ht
  regular := c.immersion t ht

def absoluteCurvature (t : ℝ) : ℝ := materialAbsoluteCurvature (c.position t) c.period

theorem energy_pos {t : ℝ} (ht : 0 ≤ t) : 0 < c.energy t :=
  (c.regularPositionAt ht).material_energy_pos

theorem absoluteCurvature_lower {t : ℝ} (ht : 0 ≤ t) : 1 ≤ c.absoluteCurvature t :=
  (c.regularPositionAt ht).material_absolute_curvature_lower

theorem stress_coercivity {t : ℝ} (ht : 0 ≤ t) (u : ℝ) :
    (1 / 16777216 : ℝ) * |curvature (c.position t) u| ^ 6 ≤
      c.energy t * c.dissipation t :=
  (c.regularPositionAt ht).material_stress_coercivity u

theorem absolute_curvature_coercivity {t : ℝ} (ht : 0 ≤ t) :
    (1 / 262144 : ℝ) * c.energy t ^ 5 / c.absoluteCurvature t ^ 6 ≤ c.dissipation t :=
  (c.regularPositionAt ht).material_absolute_curvature_coercivity

end ForwardImmersion
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
  logInfo m!"Actual material and flow-slice coercivity: {count} declarations, standard axioms only."
