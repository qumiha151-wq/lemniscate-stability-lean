import Migration.StripCurvature
import Mathlib.Tactic.FunProp

noncomputable section
open Set MeasureTheory
open scoped ContDiff ComplexConjugate
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow

private theorem rotation_speed {γ : ℝ → ℂ} (hs : ContDiff ℝ ∞ γ) {w : ℂ} (hw : ‖w‖ = 1)
    (u : ℝ) : speed (fun x => w*γ x) u = speed γ u := by
  have hd := ((hs.differentiable (by simp) u).hasDerivAt.const_mul w).deriv
  simp only [speed,hd,norm_mul,hw,one_mul]

private theorem rotation_tangent {γ : ℝ → ℂ} (hs : ContDiff ℝ ∞ γ) {w : ℂ} (hw : ‖w‖ = 1) :
    tangent (fun x => w*γ x) = fun x => w*tangent γ x := by
  funext u
  have hd := ((hs.differentiable (by simp) u).hasDerivAt.const_mul w).deriv
  simp only [tangent,arcDerivative,rotation_speed hs hw,hd,Complex.real_smul]
  ring

private theorem rotation_curvature {γ : ℝ → ℂ} (hs : ContDiff ℝ ∞ γ)
    (hr : ∀ u, deriv γ u ≠ 0) {w : ℂ} (hw : ‖w‖ = 1) (u : ℝ) :
    curvature (fun x => w*γ x) u = curvature γ u := by
  have hd := ((((tangent_smooth hs hr).differentiable (by simp) u).hasDerivAt).const_mul w).deriv
  have hnorm := Complex.mul_conj w
  rw [Complex.normSq_eq_norm_sq,hw] at hnorm
  have hcancel : conj w * w = 1 := by simpa [mul_comm,Complex.ofReal_one] using hnorm
  simp only [curvature,rotation_tangent hs hw,hd,rotation_speed hs hw,map_mul]
  rw [show conj w * conj (tangent γ u) * (w * deriv (tangent γ) u) =
    (conj w*w)*(conj (tangent γ u)*deriv (tangent γ) u) by ring,hcancel,one_mul]

namespace SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

private def rotateForWidth (w : ℂ) (hw : ‖w‖=1) : SmoothPeriodicImmersion I where
  time_open := c.time_open
  period := c.period
  period_pos := c.period_pos
  position t u := w*c.position t u
  joint_smooth := contDiffOn_const.mul c.joint_smooth
  periodic t ht u := congrArg (fun z => w*z) (c.periodic t ht u)
  immersion t ht u := by
    rw [(((c.position_slice_smooth ht).differentiable (by simp) u).hasDerivAt.const_mul w).deriv]
    exact mul_ne_zero (norm_ne_zero_iff.mp (by rw [hw]; norm_num)) (c.immersion t ht u)

/-- The true signed height extents in each physical unit direction multiply
with the position-defined energy to give at least two. -/
theorem directional_width_range {t : ℝ} (ht : t∈I) (e : ℂ) (he : ‖e‖=1) :
    ∃ lo hi : ℝ, c.HasHeightRange (innerSL ℝ e) t lo hi ∧ 2 ≤ c.bending t*(hi-lo) := by
  let w := Complex.I*conj e
  have hw : ‖w‖=1 := by simp [w,he]
  let r := c.rotateForWidth w hw
  have hpos (u : ℝ) : (r.position t u).im = inner ℝ e (c.position t u) := by
    change (w*c.position t u).im=_
    rw [Complex.inner]
    simp only [w,Complex.mul_im,Complex.mul_re,Complex.I_re,Complex.I_im,
      Complex.conj_re,Complex.conj_im]
    ring
  have hE : r.bending t = c.bending t := by
    unfold bending
    congr 1
    apply intervalIntegral.integral_congr
    intro u _
    change curvature (fun x => w*c.position t x) u ^2*speed (fun x => w*c.position t x) u = _
    rw [rotation_curvature (c.position_slice_smooth ht) (c.immersion t ht) hw,
      rotation_speed (c.position_slice_smooth ht) hw]
  have hz := r.height_range_of_slice_continuous (r.position_slice_smooth ht).continuous
  have hb := r.bending_mul_verticalWidth ht
  rw [hE] at hb
  refine ⟨r.bottom t,r.top t,?_,hb⟩
  have hproj (u : ℝ) : Complex.imCLM (r.position t u) = (innerSL ℝ e) (c.position t u) := hpos u
  rcases hz with ⟨hz,⟨a,ha,has⟩,⟨b,hb',hbs⟩⟩
  exact ⟨fun u hu => hproj u ▸ hz u hu,⟨a,ha,(hproj a).symm.trans has⟩,
    ⟨b,hb',(hproj b).symm.trans hbs⟩⟩

theorem bending_pos_of_width {t : ℝ} (ht : t∈I) : 0 < c.bending t := by
  have h := c.bending_mul_verticalWidth ht
  by_contra! hz
  rw [le_antisymm hz (c.bending_nonneg t),zero_mul] at h
  norm_num at h

#print axioms directional_width_range
end SmoothPeriodicImmersion
end MigrationGeometry.Flow
