import SolitonClassification.ReflectedGeometry
import SolitonClassification.Rotating.RotatingNormalEvolutionCurvature
import SolitonClassification.Rotating.RotatingNormalEvolutionClock

/-! The homothetically expanding position has the elastic normal velocity
in physical time. All spatial derivatives here are taken on the actual slice. -/
noncomputable section
namespace ClosedSimilarity.ReflectedArc.ZeroTurnExpander
open SolitonClassification.Rotating.NormalEvolution
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
variable {L b : ℝ} (z : ZeroTurnExpander L b)

def scaled (r : ℝ) (u : ℝ → ℝ) (s : ℝ) := r*u s

private theorem scale_deriv (r : ℝ) {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) :
    deriv (scaled r u) = scaled r (deriv u) :=
  funext fun s => (((hu.differentiable (by simp) s).hasDerivAt).const_mul r).deriv

theorem scaled_speed {r : ℝ} (hr : 0<r) (s : ℝ) :
    curveSpeed (scaled r z.X) (scaled r z.Y) s=r := by
  rw [curveSpeed,scale_deriv r z.X_smooth,scale_deriv r z.Y_smooth]
  simp only [scaled,mul_pow,←mul_add,z.unit_speed,mul_one,Real.sqrt_sq hr.le]

theorem scaled_curvature {r : ℝ} (hr : 0<r) :
    intrinsicCurvature (scaled r z.X) (scaled r z.Y) = fun s => z.k s/r := by
  funext s
  rw [intrinsicCurvature,z.scaled_speed hr,scale_deriv r z.X_smooth,scale_deriv r z.Y_smooth,
    scale_deriv r ((contDiff_infty_iff_deriv.mp z.X_smooth).2),
    scale_deriv r ((contDiff_infty_iff_deriv.mp z.Y_smooth).2),←z.curvature s]
  simp only [scaled]
  field_simp [hr.ne']

theorem scaled_force {r : ℝ} (hr : 0<r) (s : ℝ) :
    intrinsicElasticForce (scaled r z.X) (scaled r z.Y) s =
      (deriv (deriv z.k) s + z.k s^3/2)/r^3 := by
  have dk := z.k_smooth.differentiable (by simp)
  have dv := (contDiff_infty_iff_deriv.mp z.k_smooth).2.differentiable (by simp)
  have da : arcDerivative (scaled r z.X) (scaled r z.Y)
      (intrinsicCurvature (scaled r z.X) (scaled r z.Y)) = fun t => deriv z.k t/r/r := by
    funext t
    rw [arcDerivative,z.scaled_speed hr,z.scaled_curvature hr,((dk t).hasDerivAt.div_const r).deriv]
  rw [intrinsicElasticForce,da,arcDerivative,z.scaled_speed hr,z.scaled_curvature hr,
    (((dv s).hasDerivAt.div_const r).div_const r).deriv]
  field_simp [hr.ne']

/-- In the natural similarity parametrization, the physical normal component
agrees with the force computed intrinsically from the moving curve. -/
theorem homothetic_normal_velocity {t : ℝ} (ht : -1/4<t) (s : ℝ) :
    let X := fun u => scaled (dilationScale u) z.X
    let Y := fun u => scaled (dilationScale u) z.Y
    deriv (fun u => X u s) t * unitNormalX (X t) (Y t) s +
      deriv (fun u => Y u s) t * unitNormalY (X t) (Y t) s =
        -intrinsicElasticForce (X t) (Y t) s := by
  dsimp only
  have dr : HasDerivAt dilationScale (1/(dilationScale t)^3) t := by
    have eq : Real.exp (logClock t)*Real.exp (-4*logClock t)=1/(dilationScale t)^3 := by
      rw [dilationScale,one_div,←Real.exp_nat_mul,←Real.exp_neg,←Real.exp_add]
      congr 1
      ring
    rw [←eq]
    exact (logClock_hasDerivAt ht).exp
  have dx : deriv (fun u => scaled (dilationScale u) z.X s) t =
      (1/(dilationScale t)^3)*z.X s := (dr.mul_const _).deriv
  have dy : deriv (fun u => scaled (dilationScale u) z.Y s) t =
      (1/(dilationScale t)^3)*z.Y s := (dr.mul_const _).deriv
  rw [dx,dy,unitNormalX,unitNormalY,z.scaled_speed (dilationScale_pos t),
    scale_deriv _ z.X_smooth,scale_deriv _ z.Y_smooth,z.scaled_force (dilationScale_pos t),
    z.dilation_equation s]
  simp only [scaled]
  field_simp [(dilationScale_pos t).ne']

end ClosedSimilarity.ReflectedArc.ZeroTurnExpander
