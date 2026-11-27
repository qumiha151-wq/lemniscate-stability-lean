import LengthGrowth.ActualFlow.EventualCurvatureSign
import LengthGrowth.ActualFlow.MaterialWeightedRate

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow

/-- Signed angle swept between two material labels. -/
def arcTurn (γ : ℝ → ℂ) (a b : ℝ) : ℝ := ∫ u in a..b, curvature γ u * speed γ u

namespace SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)
theorem arcTurn_hasDerivAt {t : ℝ} (ht : t ∈ I) (a b : ℝ) :
    HasDerivAt (fun x => arcTurn (c.position x) a b) (c.velocityGradientNormal t b-c.velocityGradientNormal t a) t := by
  have h := hasDerivAt_intervalIntegral_of_jointC1 (a := a) (b := b)
    (F := fun t u => curvature (c.position t) u * speed (c.position t) u)
    c.time_open ((c.curvature_joint_smooth.mul c.speed_joint_smooth).of_le (by simp)) ht
  have hi : (∫ u in a..b, deriv (fun x =>
      curvature (c.position x) u * speed (c.position x) u) t) =
      ∫ u in a..b, deriv (c.velocityGradientNormal t) u := by
    apply intervalIntegral.integral_congr
    intro u _
    have hk := joint_smooth_time_hasDerivAt c.time_open
      (f := fun x => curvature (c.position x)) c.curvature_joint_smooth ht u
    have hg := joint_smooth_time_hasDerivAt c.time_open
      (f := fun x => speed (c.position x)) c.speed_joint_smooth ht u
    calc
      _ = _ := (hk.mul hg).deriv
      _ = _ := by linarith only [c.curvature_metric_time_identity ht u]
  have hb := joint_smooth_space_slice (f := c.velocityGradientNormal)
    c.velocityGradientNormal_joint_smooth ht
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
    (fun u _ => (hb.differentiable (by simp) u).hasDerivAt)
    ((contDiff_infty_iff_deriv.mp hb).2.continuous.intervalIntegrable _ _)
  rw [hi,hft] at h
  exact h
theorem arcTurn_frameRate (hf : c.IsNormalFEF) {t : ℝ} (ht : t∈I) (u : ℝ) :
    c.velocityGradientNormal t u = -arcDerivative (c.position t) (force (c.position t)) u ∧
    c.velocityGradientTangent t u = curvature (c.position t) u*force (c.position t) u := by
  let x := c.position t
  have reg := c.immersion t ht
  have smooth := c.position_slice_smooth ht
  have cf := force_smooth smooth reg
  have hv : c.velocity t = fun s => (-force x s) • normal x s := by
    funext s
    simpa only [Complex.real_smul,Complex.ofReal_neg] using c.normal_velocity_eq hf ht s
  have df : HasDerivAt (force x) (deriv (force x) u) u := (cf.differentiable (by simp) u).hasDerivAt
  have dn : HasDerivAt (normal x) ((-(speed x u*curvature x u)) • tangent x u) u := by
    simpa only [Complex.real_smul,Complex.ofReal_neg] using normal_hasDerivAt smooth reg u
  have der := df.neg.smul dn
  change HasDerivAt (fun s => -force x s • normal x s)
    ((-force x u) • (-(speed x u*curvature x u)) • tangent x u +
      (-deriv (force x) u) • normal x u) u at der
  have ort := tangent_normal_orthogonal (γ:=x) u
  have rev : inner ℝ (normal x u) (tangent x u)=0 := by rw [real_inner_comm,ort]
  change inner ℝ (arcDerivative x (c.velocity t) u) (normal x u) = -arcDerivative x (force x) u ∧
    inner ℝ (arcDerivative x (c.velocity t) u) (tangent x u) = curvature x u*force x u
  rw [hv]
  simp only [arcDerivative,der.deriv,inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq,
    normal_unit (γ:=x) reg,tangent_unit (γ:=x) reg,ort,rev,smul_eq_mul]
  constructor <;> field_simp [(speed_pos (γ:=x) reg u).ne'] <;> ring

theorem arcTurn_time_flux (hf : c.IsNormalFEF) {t : ℝ} (ht : t∈I) (a b : ℝ) :
    HasDerivAt (fun x => arcTurn (c.position x) a b)
      (arcDerivative (c.position t) (force (c.position t)) a -
       arcDerivative (c.position t) (force (c.position t)) b) t := by
  have h := c.arcTurn_hasDerivAt ht a b
  rw [(c.arcTurn_frameRate hf ht b).1,(c.arcTurn_frameRate hf ht a).1] at h
  convert h using 1; ring

end SmoothPeriodicImmersion
end LengthGrowth.ActualFlow
#print axioms LengthGrowth.ActualFlow.SmoothPeriodicImmersion.arcTurn_time_flux
