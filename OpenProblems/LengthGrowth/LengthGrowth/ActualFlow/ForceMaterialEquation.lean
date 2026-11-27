import LengthGrowth.ActualFlow.MaterialTurnFlux
import LengthGrowth.ActualFlow.ForcePersistence

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow

/-- Pure-normal material time rate of signed curvature, as a function of a slice. -/
def bendingRate (x : ℝ → ℂ) (u : ℝ) : ℝ :=
  -arcDerivative x (arcDerivative x (force x)) u-(curvature x u)^2*force x u

/-- The metric commutator contribution is included in the material rate of
the arclength derivative of curvature. -/
def bendingGradientRate (x : ℝ → ℂ) (u : ℝ) : ℝ :=
  arcDerivative x (bendingRate x) u-curvature x u*force x u*curvatureGradient x u

namespace SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem scalar_arc_time_commutator {f : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => f z.1 z.2) (I ×ˢ (univ : Set ℝ)))
    {t : ℝ} (ht : t∈I) (u : ℝ) :
    HasDerivAt (fun v => arcDerivative (c.position v) (f v) u)
      (arcDerivative (c.position t) (fun y => deriv (fun v => f v y) t) u -
        c.velocityGradientTangent t u*arcDerivative (c.position t) (f t) u) t := by
  have df := joint_smooth_time_hasDerivAt c.time_open
    (f:=fun v => deriv (f v)) (joint_smooth_deriv_space c.time_open h) ht u
  rw [actual_time_space_deriv_commute c.time_open h ht u] at df
  have g := c.speed_time_hasDerivAt ht u
  have gp := (speed_pos (c.immersion t ht) u).ne'
  convert! (g.inv gp).mul df using 1
  simp only [arcDerivative,smul_eq_mul,Pi.inv_apply]
  field_simp [gp]
  ring

theorem intrinsic_bending_rate (flow : c.IsNormalFEF) {t : ℝ} (ht : t∈I) (u : ℝ) :
    HasDerivAt (fun v => curvature (c.position v) u) (bendingRate (c.position t) u) t := by
  have df := c.curvature_time_hasDerivAt ht u
  have vel : c.velocityGradientNormal t = fun y => -arcDerivative (c.position t) (force (c.position t)) y :=
    funext fun y => (c.arcTurn_frameRate flow ht y).1
  rw [vel,(c.arcTurn_frameRate flow ht u).2] at df
  have reg := c.immersion t ht
  have sm := c.position_slice_smooth ht
  have d := ((arcDerivative_smooth sm reg (force_smooth sm reg)).differentiable (by simp) u).hasDerivAt.neg
  change HasDerivAt (fun y => -arcDerivative (c.position t) (force (c.position t)) y)
    (-deriv (arcDerivative (c.position t) (force (c.position t))) u) u at d
  rw [d.deriv] at df
  convert df using 1
  unfold bendingRate arcDerivative
  simp only [smul_eq_mul,div_eq_mul_inv]
  ring

theorem intrinsic_bending_gradient_rate (flow : c.IsNormalFEF) {t : ℝ} (ht : t∈I) (u : ℝ) :
    HasDerivAt (fun v => curvatureGradient (c.position v) u)
      (bendingGradientRate (c.position t) u) t := by
  have h := c.scalar_arc_time_commutator (f:=fun v => curvature (c.position v)) c.curvature_joint_smooth ht u
  rw [show (fun y => deriv (fun v => curvature (c.position v) y) t) = bendingRate (c.position t)
    from funext fun y => (c.intrinsic_bending_rate flow ht y).deriv,(c.arcTurn_frameRate flow ht u).2] at h
  exact h

/-- The material derivative of the actual elastic force in divergence form.
The smooth immersion and its pure-normal evolution determine every term. -/
theorem elastic_force_material_rate (flow : c.IsNormalFEF) {t : ℝ} (ht : t∈I) (u : ℝ) :
    let x := c.position t
    HasDerivAt (fun v => force (c.position v) u)
      (arcDerivative x (bendingGradientRate x) u-curvature x u*force x u*curvatureSecond x u+
        3/2*(curvature x u)^2*bendingRate x u) t := by
  have h := c.scalar_arc_time_commutator (f:=fun v => curvatureGradient (c.position v))
    (c.arcDerivative_joint_smooth (f:=fun v => curvature (c.position v)) c.curvature_joint_smooth) ht u
  have eqn : (fun y => deriv (fun v => curvatureGradient (c.position v) y) t) =
    bendingGradientRate (c.position t) := funext fun y => (c.intrinsic_bending_gradient_rate flow ht y).deriv
  rw [eqn,(c.arcTurn_frameRate flow ht u).2] at h
  convert! h.add (((c.intrinsic_bending_rate flow ht u).pow 3).div_const 2) using 1
  unfold curvatureSecond
  ring

end SmoothPeriodicImmersion
end LengthGrowth.ActualFlow
#print axioms LengthGrowth.ActualFlow.SmoothPeriodicImmersion.elastic_force_material_rate
