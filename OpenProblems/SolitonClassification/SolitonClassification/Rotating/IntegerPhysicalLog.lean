import SolitonClassification.Rotating.RotatingNormalEvolution
import SolitonClassification.Rotating.IntegerClosedImmersion

namespace SolitonClassification.Rotating.IntegerTarget.Physical
noncomputable section
open Set Real MeasureTheory NormalEvolution
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

structure Seed where
  b : ℝ
  L : ℝ
  I : WindingOneImmersion b L
  positive : 0<L

def physicalField (P : Seed) : PeriodicScalarField :=
  profileReparamField P.b P.I.x P.I.y P.L P.positive P.I.smoothX P.I.smoothY P.I.periodX P.I.periodY

variable (P : Seed)

def normalParameter (τ s : ℝ) : ℝ := scalarFlow (physicalField P) τ s

def normalLogX (τ s : ℝ) : ℝ := exp τ*(cos (P.b*τ)*P.I.x (normalParameter P τ s)-
  sin (P.b*τ)*P.I.y (normalParameter P τ s))
def normalLogY (τ s : ℝ) : ℝ := exp τ*(sin (P.b*τ)*P.I.x (normalParameter P τ s)+
  cos (P.b*τ)*P.I.y (normalParameter P τ s))

def rotatedTangentX (τ s : ℝ) : ℝ :=
  cos (P.b*τ)*deriv (P.I.x) s-sin (P.b*τ)*deriv (P.I.y) s
def rotatedTangentY (τ s : ℝ) : ℝ :=
  sin (P.b*τ)*deriv (P.I.x) s+cos (P.b*τ)*deriv (P.I.y) s

def profileForce (s : ℝ) : ℝ := deriv (deriv (P.I.k)) s+(P.I.k s)^3/2

theorem profileForce_eq (s : ℝ) : profileForce P s=
    -normalSupport (P.I.x) (P.I.y) s-P.b*tangentSupport (P.I.x) (P.I.y) s :=
  P.I.soliton s

theorem normalParameter_joint_smooth :
    ContDiff ℝ ∞ (fun z : ℝ×ℝ => normalParameter P z.1 z.2) :=
  scalarFlow_joint_smooth _

theorem normalLogX_joint_smooth : ContDiff ℝ ∞ (fun z : ℝ×ℝ => normalLogX P z.1 z.2) := by
  exact contDiff_fst.exp.mul (((contDiff_const.mul contDiff_fst).cos.mul
    (P.I.smoothX.comp (normalParameter_joint_smooth P))).sub
    ((contDiff_const.mul contDiff_fst).sin.mul (P.I.smoothY.comp (normalParameter_joint_smooth P))))

theorem normalLogY_joint_smooth : ContDiff ℝ ∞ (fun z : ℝ×ℝ => normalLogY P z.1 z.2) := by
  exact contDiff_fst.exp.mul (((contDiff_const.mul contDiff_fst).sin.mul
    (P.I.smoothX.comp (normalParameter_joint_smooth P))).add
    ((contDiff_const.mul contDiff_fst).cos.mul (P.I.smoothY.comp (normalParameter_joint_smooth P))))

theorem normalParameter_period_add (τ s : ℝ) :
    normalParameter P τ (s+P.L)=normalParameter P τ s+P.L :=
  scalarFlow_period_add _ τ s

theorem normalLogX_periodic (τ : ℝ) : Function.Periodic (normalLogX P τ) P.L := by
  intro s
  simp only [normalLogX,normalParameter_period_add]
  rw [P.I.periodX _,P.I.periodY _]

theorem normalLogY_periodic (τ : ℝ) : Function.Periodic (normalLogY P τ) P.L := by
  intro s
  simp only [normalLogY,normalParameter_period_add]
  rw [P.I.periodX _,P.I.periodY _]

theorem normalLogX_initial (s : ℝ) : normalLogX P 0 s=P.I.x s := by
  simp [normalLogX,normalParameter,scalarFlow_zero]
theorem normalLogY_initial (s : ℝ) : normalLogY P 0 s=P.I.y s := by
  simp [normalLogY,normalParameter,scalarFlow_zero]

theorem normalLogX_spatial_derivative (τ s : ℝ) :
    HasDerivAt (normalLogX P τ)
      (exp τ*scalarJacobian (physicalField P) τ s*
        rotatedTangentX P τ (normalParameter P τ s)) s := by
  have hx := ((P.I.smoothX.differentiable (by simp)) _).hasDerivAt.scomp s
    (scalarFlow_hasDerivAt_initial (physicalField P) τ s)
  have hy := ((P.I.smoothY.differentiable (by simp)) _).hasDerivAt.scomp s
    (scalarFlow_hasDerivAt_initial (physicalField P) τ s)
  convert! ((hx.const_mul (cos (P.b*τ))).sub (hy.const_mul (sin (P.b*τ)))).const_mul (exp τ) using 1
  dsimp [rotatedTangentX,normalParameter]
  ring

theorem normalLogY_spatial_derivative (τ s : ℝ) :
    HasDerivAt (normalLogY P τ)
      (exp τ*scalarJacobian (physicalField P) τ s*
        rotatedTangentY P τ (normalParameter P τ s)) s := by
  have hx := ((P.I.smoothX.differentiable (by simp)) _).hasDerivAt.scomp s
    (scalarFlow_hasDerivAt_initial (physicalField P) τ s)
  have hy := ((P.I.smoothY.differentiable (by simp)) _).hasDerivAt.scomp s
    (scalarFlow_hasDerivAt_initial (physicalField P) τ s)
  convert! ((hx.const_mul (sin (P.b*τ))).add (hy.const_mul (cos (P.b*τ)))).const_mul (exp τ) using 1
  dsimp [rotatedTangentY,normalParameter]
  ring

theorem rotatedTangent_unit (τ s : ℝ) : rotatedTangentX P τ s^2+rotatedTangentY P τ s^2=1 := by
  have hu := P.I.speed s
  have ht := sin_sq_add_cos_sq (P.b*τ)
  calc
    _ = (sin (P.b*τ)^2+cos (P.b*τ)^2)*
      (deriv (P.I.x) s^2+deriv (P.I.y) s^2) := by dsimp [rotatedTangentX,rotatedTangentY]; ring
    _ = 1 := by rw [hu,ht]; ring

theorem normalLog_metric (τ s : ℝ) :
    deriv (normalLogX P τ) s^2+deriv (normalLogY P τ) s^2=
      (exp τ*scalarJacobian (physicalField P) τ s)^2 := by
  rw [(normalLogX_spatial_derivative P τ s).deriv,(normalLogY_spatial_derivative P τ s).deriv]
  calc
    _ = (exp τ*scalarJacobian (physicalField P) τ s)^2*
      (rotatedTangentX P τ (normalParameter P τ s)^2+
        rotatedTangentY P τ (normalParameter P τ s)^2) := by ring
    _ = _ := by rw [rotatedTangent_unit P,mul_one]

theorem normalLog_immersion (τ s : ℝ) :
    0<deriv (normalLogX P τ) s^2+deriv (normalLogY P τ) s^2 := by
  rw [normalLog_metric]
  exact sq_pos_of_pos (mul_pos (exp_pos _) (scalarJacobian_pos _ _ _))

theorem normalLogX_time_derivative (τ s : ℝ) :
    HasDerivAt (fun u => normalLogX P u s)
      (exp τ*profileForce P (normalParameter P τ s)*
        rotatedTangentY P τ (normalParameter P τ s)) τ := by
  let z := normalParameter P τ s
  let g := physicalField P
  have hx := ((P.I.smoothX.differentiable (by simp)) _).hasDerivAt.scomp τ (scalarFlow_hasDerivAt g s τ)
  have hy := ((P.I.smoothY.differentiable (by simp)) _).hasDerivAt.scomp τ (scalarFlow_hasDerivAt g s τ)
  have hb := (hasDerivAt_id τ).const_mul (P.b)
  have hd := (hasDerivAt_exp τ).mul ((hb.cos.mul hx).sub (hb.sin.mul hy))
  have hax := normal_velocity_algebra_x (P.b) (P.I.x z) (P.I.y z)
    (deriv (P.I.x) z) (deriv (P.I.y) z) (P.I.speed z)
  have hay := normal_velocity_algebra_y (P.b) (P.I.x z) (P.I.y z)
    (deriv (P.I.x) z) (deriv (P.I.y) z) (P.I.speed z)
  convert! hd using 1
  change exp τ*profileForce P z*rotatedTangentY P τ z=_
  rw [profileForce_eq P]
  dsimp [rotatedTangentY,normalSupport,tangentSupport,g,physicalField,profileReparamField,
    reparamVelocity,normalParameter,z] at hax hay ⊢
  linear_combination -(exp τ*cos (P.b*τ))*hax+(exp τ*sin (P.b*τ))*hay

theorem normalLogY_time_derivative (τ s : ℝ) :
    HasDerivAt (fun u => normalLogY P u s)
      (-exp τ*profileForce P (normalParameter P τ s)*
        rotatedTangentX P τ (normalParameter P τ s)) τ := by
  let z := normalParameter P τ s
  let g := physicalField P
  have hx := ((P.I.smoothX.differentiable (by simp)) _).hasDerivAt.scomp τ (scalarFlow_hasDerivAt g s τ)
  have hy := ((P.I.smoothY.differentiable (by simp)) _).hasDerivAt.scomp τ (scalarFlow_hasDerivAt g s τ)
  have hb := (hasDerivAt_id τ).const_mul (P.b)
  have hd := (hasDerivAt_exp τ).mul ((hb.sin.mul hx).add (hb.cos.mul hy))
  have hax := normal_velocity_algebra_x (P.b) (P.I.x z) (P.I.y z)
    (deriv (P.I.x) z) (deriv (P.I.y) z) (P.I.speed z)
  have hay := normal_velocity_algebra_y (P.b) (P.I.x z) (P.I.y z)
    (deriv (P.I.x) z) (deriv (P.I.y) z) (P.I.speed z)
  convert! hd using 1
  change -exp τ*profileForce P z*rotatedTangentX P τ z=_
  rw [profileForce_eq P]
  dsimp [rotatedTangentX,normalSupport,tangentSupport,g,physicalField,profileReparamField,
    reparamVelocity,normalParameter,z] at hax hay ⊢
  linear_combination -(exp τ*sin (P.b*τ))*hax-(exp τ*cos (P.b*τ))*hay

end
end SolitonClassification.Rotating.IntegerTarget.Physical
#print axioms SolitonClassification.Rotating.IntegerTarget.Physical.normalLogX_time_derivative
