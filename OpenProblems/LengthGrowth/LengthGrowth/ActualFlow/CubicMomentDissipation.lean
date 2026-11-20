import LengthGrowth.ActualFlow.CubicMomentGrowth

/-! An exact square decomposition for dissipation of curvature oscillation.
All terms are computed on the arbitrary-speed actual material curve. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth.ActualFlow

theorem integral_weighted_affine_square {k f g : ℝ → ℝ}
    (hk : Continuous k) (hf : Continuous f) (hg : Continuous g) (P a b d : ℝ) :
    (∫ u in 0..P, (a * f u - b * k u - d)^2 * g u) =
      a^2 * (∫ u in 0..P, f u^2 * g u) +
      b^2 * (∫ u in 0..P, k u^2 * g u) + d^2 * (∫ u in 0..P, g u) +
      (-2*a*b) * (∫ u in 0..P, k u * f u * g u) +
      (-2*a*d) * (∫ u in 0..P, f u * g u) + (2*b*d) * ∫ u in 0..P, k u * g u := by
  calc
    _ = ∫ u in 0..P, a^2 * (f u^2 * g u) + b^2 * (k u^2 * g u) + d^2 * g u +
        (-2*a*b) * (k u*f u*g u) + (-2*a*d) * (f u*g u) + (2*b*d) * (k u*g u) := by
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only
      ring
    _ = _ := by
      simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
        [intervalIntegral.integral_add, intervalIntegral.integral_const_mul]

namespace ForwardImmersion
variable (c : ForwardImmersion)

def curvatureOscillation (t : ℝ) : ℝ :=
  2 * c.normalizedProduct t - materialSignedCurvature (c.position 0) c.period ^ 2

theorem curvatureOscillation_eq_integral {t : ℝ} (ht : 0 ≤ t) :
    c.curvatureOscillation t = c.length t * ∫ u in 0..c.period,
      (curvature (c.position t) u - materialSignedCurvature (c.position t) c.period /
        c.length t)^2 * speed (c.position t) u := by
  let γ := c.position t
  let S := materialSignedCurvature γ c.period
  let L := c.length t
  have hL : L ≠ 0 := (c.length_pos ht).ne'
  have hk := (curvature_smooth (c.position_slice_smooth ht) (c.immersion t ht)).continuous
  have hg := (speed_smooth (c.position_slice_smooth ht) (c.immersion t ht)).continuous
  have hid := integral_weighted_affine_square hk hk hg c.period 1 0 (S/L)
  simp only [one_mul, zero_mul, sub_zero, one_pow, zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero, mul_one] at hid
  change (∫ u in 0..c.period, (curvature γ u - S / L)^2 * speed γ u) = _ at hid
  change 2 * (c.energy t * L) - _ = L * _
  rw [← c.signedCurvature_eq_initial ht, hid]
  change 2 * (((1/2 : ℝ) * _) * L) - S^2 = L * (_ + (S/L)^2 * L + _ * S)
  field_simp [hL]
  simp only [ForwardImmersion.interior]
  ring

theorem curvatureOscillation_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ c.curvatureOscillation t := by
  rw [c.curvatureOscillation_eq_integral ht]
  exact mul_nonneg (c.length_pos ht).le
    (intervalIntegral.integral_nonneg_of_forall c.period_pos.le
      (fun u => mul_nonneg (sq_nonneg _) (speed_pos (c.immersion t ht) u).le))

theorem curvatureOscillation_hasDerivAt (hf : c.IsNormalFEF) {t : ℝ} (ht : 0 < t) :
    HasDerivAt c.curvatureOscillation
      (2 * (c.energy t * c.lengthRate t - c.length t * c.dissipation t)) t :=
  ((c.normalizedProduct_hasDerivAt_normal hf ht).const_mul 2).sub_const _

theorem curvatureOscillation_exact_squares {t : ℝ} (ht : 0 ≤ t) :
    let γ := c.position t
    let L := c.length t
    let B := 2 * c.energy t
    let C := materialCubicCurvature γ c.period
    let S := materialSignedCurvature γ c.period
    16*L^2*(L*c.dissipation t - c.energy t*c.lengthRate t) - B^2*c.curvatureOscillation t =
      L * (∫ u in 0..c.period, (4*L*force γ u - B*curvature γ u - C)^2 * speed γ u) +
      (B*S-L*C)^2 + 2*L*(L*C^2-B^3) := by
  let γ := c.position t
  let L := c.length t
  let E := c.energy t
  let C := materialCubicCurvature γ c.period
  let S := materialSignedCurvature γ c.period
  have hs := c.position_slice_smooth ht
  have hr := c.immersion t ht
  have he : (∫ u in 0..c.period, curvature γ u^2 * speed γ u) = 2*E := by
    change (∫ u in 0..c.period, curvature γ u^2 * speed γ u) =
      2*((1/2 : ℝ) * ∫ u in 0..c.period, curvature γ u^2 * speed γ u)
    ring
  have hm := integral_weighted_affine_square
    (curvature_smooth hs hr).continuous (force_smooth hs hr).continuous
    (speed_smooth hs hr).continuous c.period (4*L) (2*E) C
  change (∫ u in 0..c.period, (4*L*force γ u-2*E*curvature γ u-C)^2*speed γ u) =
    (4*L)^2*c.dissipation t + (2*E)^2*_ + C^2*L + _*c.lengthRate t +
    (-2*(4*L)*C)*(∫ u in 0..c.period, force γ u*speed γ u) + _*S at hm
  rw [he, integral_force_eq_half_cubic hs hr (c.periodic t ht)] at hm
  change 16*L^2*(L*c.dissipation t-E*c.lengthRate t) - (2*E)^2*c.curvatureOscillation t =
    L*(∫ u in 0..c.period, (4*L*force γ u-2*E*curvature γ u-C)^2*speed γ u) +
    (2*E*S-L*C)^2 + 2*L*(L*C^2-(2*E)^3)
  rw [hm, curvatureOscillation, ← c.signedCurvature_eq_initial ht]
  change 16*L^2*(L*c.dissipation t-E*c.lengthRate t) - (2*E)^2*(2*(E*L)-S^2) =
    L*((4*L)^2*c.dissipation t+(2*E)^2*(2*E)+C^2*L+_ * c.lengthRate t+
    (-2*(4*L)*C)*((1/2)*C)+_*S)+(2*E*S-L*C)^2+2*L*(L*C^2-(2*E)^3)
  ring

theorem curvatureOscillation_deriv_bound (hf : c.IsNormalFEF) {t : ℝ}
    (ht : 0 < t) (hm : c.CubicMomentDominates t) :
    8*c.length t^2 * deriv c.curvatureOscillation t ≤
      -(2*c.energy t)^2 * c.curvatureOscillation t := by
  let γ := c.position t
  let L := c.length t
  let B := 2*c.energy t
  let C := materialCubicCurvature γ c.period
  let S := materialSignedCurvature γ c.period
  have h := c.curvatureOscillation_exact_squares ht.le
  have hq : 0 ≤ ∫ u in 0..c.period, (4*L*force γ u - B*curvature γ u - C)^2 * speed γ u :=
    intervalIntegral.integral_nonneg_of_forall c.period_pos.le
      (fun u => mul_nonneg (sq_nonneg _) (speed_pos (c.immersion t ht.le) u).le)
  change 16*L^2*(L*c.dissipation t - c.energy t*c.lengthRate t) - B^2*c.curvatureOscillation t =
    L*_+(B*S-L*C)^2+2*L*(L*C^2-B^3) at h
  rw [(c.curvatureOscillation_hasDerivAt hf ht).deriv]
  change 8*L^2*(2*(c.energy t*c.lengthRate t-L*c.dissipation t)) ≤ -B^2*c.curvatureOscillation t
  have hl : 0 ≤ L := (c.length_pos ht.le).le
  change B^3 ≤ L*C^2 at hm
  nlinarith only [h, mul_nonneg hl hq, sq_nonneg (B*S-L*C), mul_nonneg hl (sub_nonneg.mpr hm)]

end ForwardImmersion
end LengthGrowth.ActualFlow

#print axioms LengthGrowth.ActualFlow.ForwardImmersion.curvatureOscillation_exact_squares
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.curvatureOscillation_deriv_bound
