import Migration.LowDefectMaterialSlab

noncomputable section
open Set MeasureTheory
open scoped ComplexConjugate ContDiff
namespace MigrationGeometry.Flow
private theorem reflected_deriv {f : ℝ→ℂ} {u : ℝ} (h : DifferentiableAt ℝ f u) :
    deriv (fun x=>conj (f x)) u=conj (deriv f u) :=
  (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt u h.hasDerivAt).deriv

theorem reflected_speed {g : ℝ→ℂ} (hg : ContDiff ℝ ∞ g) (u : ℝ) :
    speed (fun u=>conj (g u)) u=speed g u := by
  simp [speed,reflected_deriv ((hg.differentiable (by simp)) u)]

private theorem reflected_tangent {g : ℝ→ℂ} (hg : ContDiff ℝ ∞ g) :
    tangent (fun u=>conj (g u))=fun u=>conj (tangent g u) := by
  funext u
  simp [tangent,arcDerivative,reflected_speed hg,reflected_deriv ((hg.differentiable (by simp)) u),
    Complex.real_smul]

private theorem reflected_normal {g : ℝ→ℂ} (hg : ContDiff ℝ ∞ g) (u : ℝ) :
    normal (fun u=>conj (g u)) u= -conj (normal g u) := by
  simp [normal,reflected_tangent hg]

private theorem reflected_curvature {g : ℝ→ℂ} (hg : ContDiff ℝ ∞ g) (reg : ∀u,deriv g u≠0) :
    curvature (fun u=>conj (g u))=fun u=> -curvature g u := by
  funext u
  unfold curvature
  rw [reflected_tangent hg,reflected_speed hg,reflected_deriv (((tangent_smooth hg reg).differentiable (by simp)) u)]
  have h (a b : ℂ) : (conj (conj a)*conj b).im= -(conj a*b).im := by
    rw [←map_mul,Complex.conj_im]
  simp only [h,neg_div]

private theorem reflected_arc_neg {g : ℝ→ℂ} (hg : ContDiff ℝ ∞ g) (f : ℝ→ℝ) :
    arcDerivative (fun u=>conj (g u)) (fun u=> -f u)=fun u=> -arcDerivative g f u := by
  funext u
  simp [arcDerivative,reflected_speed hg,deriv.fun_neg]

private theorem reflected_force {g : ℝ→ℂ} (hg : ContDiff ℝ ∞ g) (reg : ∀u,deriv g u≠0) (u : ℝ) :
    force (fun u=>conj (g u)) u= -force g u := by
  simp only [force,curvatureSecond,curvatureGradient,reflected_curvature hg reg,reflected_arc_neg hg]
  ring

namespace SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

def reflected : SmoothPeriodicImmersion I where
  time_open := c.time_open
  period := c.period
  period_pos := c.period_pos
  position := fun t u=>conj (c.position t u)
  joint_smooth := Complex.conjCLE.contDiff.comp_contDiffOn c.joint_smooth
  periodic := fun t ht u=>congrArg _ (c.periodic t ht u)
  immersion := fun t ht u=>by
    rw [reflected_deriv (((c.position_slice_smooth ht).differentiable (by simp)) u)]
    simpa using c.immersion t ht u

theorem reflected_flow (hf : c.IsNormalFEF) : c.reflected.IsNormalFEF := by
  intro t ht u
  have hg := c.position_slice_smooth ht
  have h := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hf t ht u)
  apply h.congr_deriv
  change conj ((-force (c.position t) u) • normal (c.position t) u) =
    (-force (fun u=>conj (c.position t u)) u) • normal (fun u=>conj (c.position t u)) u
  simp [reflected_normal hg,reflected_force hg (c.immersion t ht),Complex.real_smul]

theorem reflected_turn {t : ℝ} (ht : t∈I) : c.reflected.signedCurvatureIntegral t= -c.signedCurvatureIntegral t := by
  unfold signedCurvatureIntegral
  rw [←intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro u _
  simp [reflected,reflected_curvature (c.position_slice_smooth ht) (c.immersion t ht),reflected_speed (c.position_slice_smooth ht)]

theorem reflected_bending {t : ℝ} (ht : t∈I) : c.reflected.bending t=c.bending t := by
  unfold bending
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  simp [reflected,reflected_curvature (c.position_slice_smooth ht) (c.immersion t ht),reflected_speed (c.position_slice_smooth ht)]

theorem reflected_length {t : ℝ} (ht : t∈I) : c.reflected.coreLength t=c.coreLength t := by
  apply intervalIntegral.integral_congr
  exact fun u _=>reflected_speed (c.position_slice_smooth ht) u

end SmoothPeriodicImmersion
end MigrationGeometry.Flow
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.reflected_flow
