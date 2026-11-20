import LengthGrowth.ActualFlow.AmbientCoercivity

/-! Disk energy in the original material parameter, with its speed density. -/
noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow

def materialDiskEnergy (γ : ℝ → ℂ) (P : ℝ) (p : ℂ) (R : ℝ) : ℝ :=
  ∫ u in 0..P, (γ ⁻¹' Metric.closedBall p R).indicator (fun y => curvature γ y^2 / 2) u * speed γ u

theorem PeriodicRegularPosition.closedFrenetCurve_diskEnergy (a : PeriodicRegularPosition)
    (p : ℂ) (R : ℝ) : a.closedFrenetCurve.diskEnergy p R = materialDiskEnergy a.position a.period p R := by
  let b := a.closedFrenetCurve
  let f := (b.curve ⁻¹' Metric.closedBall p R).indicator (fun s => b.curvature s^2/2)
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (a:=0) (b:=a.period)
    (f:=a.arclength) (f':=speed a.position) (g:=f) a.arclength_smooth.continuous.continuousOn
    (fun u _ => a.arclength_hasDerivAt u) (fun u _ => (speed_pos a.regular u).le)
  rw [a.arclength_zero, a.arclength_length] at h
  change (∫ s in 0..a.length, f s) = _
  rw [← h]
  apply intervalIntegral.integral_congr
  intro u _
  have hpos : b.curve (a.arclength u) = a.position u := by
    change a.position (a.arclengthInverse (a.arclength u)) = a.position u
    rw [a.arclength_inverse_right]
  have hk : b.curvature (a.arclength u) = curvature a.position u := by
    rw [a.closedFrenetCurve_curvature,a.arclength_inverse_right]
  by_cases hin : a.position u ∈ Metric.closedBall p R
  · have hm : a.arclength u ∈ b.curve ⁻¹' Metric.closedBall p R := by simpa only [mem_preimage,hpos] using hin
    simp only [Function.comp_apply,f,indicator_of_mem hm, indicator_of_mem (show u ∈ a.position ⁻¹' Metric.closedBall p R from hin),hk]
  · have hm : a.arclength u ∉ b.curve ⁻¹' Metric.closedBall p R := by simpa only [mem_preimage,hpos] using hin
    simp only [Function.comp_apply,f,indicator_of_notMem hm, indicator_of_notMem (show u ∉ a.position ⁻¹' Metric.closedBall p R from hin)]

theorem ForwardImmersion.quarter_length_iff_material_disk_energy (c : ForwardImmersion)
    (hflow : c.IsNormalFEF) : c.HasQuarterLengthBound ↔
      ∃ R θ : ℝ, 0<R ∧ 0<θ ∧ ∀ t, 0≤t → ∃ p,
        θ*c.energy t ≤ materialDiskEnergy (c.position t) c.period p (R/c.energy t) := by
  rw [c.quarter_length_iff_ambient_concentration hflow]
  unfold ForwardImmersion.HasAmbientEnergyConcentration
  simp_rw [PeriodicRegularPosition.closedFrenetCurve_diskEnergy]
  rfl

end LengthGrowth.ActualFlow
