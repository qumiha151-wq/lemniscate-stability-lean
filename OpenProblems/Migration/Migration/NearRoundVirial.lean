import Migration.NearRoundSupport

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

def arclengthCentroid (t : ℝ) : ℂ := (c.coreLength t)⁻¹ •
  (∫ u in 0..c.period, speed (c.position t) u • c.position t u)

theorem map_arclengthCentroid (H : ℂ →L[ℝ] ℝ) {t : ℝ} (ht : t ∈ I) :
    H (c.arclengthCentroid t) = c.centroidHeight H t := by
  have hs := c.position_slice_smooth ht
  have hg := (speed_smooth hs (c.immersion t ht)).continuous
  rw [arclengthCentroid, map_smul, ← H.intervalIntegral_comp_comm
    (f := fun u => speed (c.position t) u • c.position t u) (μ := volume)
    ((hg.smul hs.continuous).intervalIntegrable 0 c.period)]
  simp only [map_smul, smul_eq_mul, centroidHeight,cutoffMass,id_eq,div_eq_inv_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  ring

theorem signed_normal_support_bounds {t S a u : ℝ} (ht : t ∈ I) (hS : 0 < S)
    (ha : 0 ≤ a) (ho : c.curvatureOscillation S t ≤ a^2) (hu : u ∈ Icc 0 c.period) :
    -(1+a)*c.coreLength t/S ≤ inner ℝ (normal (c.position t) u)
      (c.position t u - c.arclengthCentroid t) ∧
    inner ℝ (normal (c.position t) u) (c.position t u - c.arclengthCentroid t) ≤
      -(1-a)*c.coreLength t/S := by
  let H := innerSL ℝ (normal (c.position t) u)
  have hn := normal_unit (c.immersion t ht) u
  have hH : ‖H‖ ≤ 1 := by dsimp [H]; rw [innerSL_apply_norm, hn]
  have h := abs_le.mp (c.height_normal_defect H hH ht hS ha ho hu)
  rw [← c.map_arclengthCentroid H ht, ← map_sub] at h
  simp only [H, innerSL_apply_apply, real_inner_self_eq_norm_sq, hn, one_pow] at h
  have hL := c.coreLength_pos ht
  have h1 := mul_le_mul_of_nonneg_right h.1 (mul_nonneg hL.le hS.le)
  have h2 := mul_le_mul_of_nonneg_right h.2 (mul_nonneg hL.le hS.le)
  field_simp [hL.ne',hS.ne'] at h1 h2
  constructor
  · apply (div_le_iff₀ hS).mpr; linarith
  · apply (le_div_iff₀ hS).mpr; linarith

/-- Physical dilation identity, relative to any fixed spatial origin,
for an arbitrary-speed slice. -/
theorem material_virial {t : ℝ} (ht : t ∈ I) (p : ℂ) :
    (∫ u in 0..c.period, speed (c.position t) u * force (c.position t) u *
      inner ℝ (normal (c.position t) u) (c.position t u - p)) = -c.bending t := by
  let γ := c.position t
  let V := fun u => γ u-p
  have hs := c.position_slice_smooth ht
  have hr := c.immersion t ht
  have hp := c.periodic t ht
  have hv : ContDiff ℝ ∞ V := hs.sub contDiff_const
  have hpv : Function.Periodic V c.period := fun u => by dsimp [V,γ]; rw [hp u]
  have h := stress_spatial_first_variation hs hr hp hv hpv
  change _ = -c.bending t
  rw [← h]
  congr 1
  unfold bending
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro u _
  have hd : deriv V u = speed γ u • tangent γ u :=
    ((position_hasDerivAt hs hr u).sub_const p).deriv
  have hstress : stress γ u = (curvature γ u^2/2) • tangent γ u +
      curvatureGradient γ u • normal γ u := by
    simp [stress, Complex.real_smul]
  change inner ℝ (stress γ u) (deriv V u) = curvature γ u^2*speed γ u/2
  rw [hd, hstress, real_inner_smul_right, inner_add_left,
    real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq, tangent_unit hr,
    ← real_inner_comm (normal γ u) (tangent γ u), tangent_normal_orthogonal]
  ring

#print axioms map_arclengthCentroid
#print axioms signed_normal_support_bounds
#print axioms material_virial
end MigrationGeometry.Flow.SmoothPeriodicImmersion
