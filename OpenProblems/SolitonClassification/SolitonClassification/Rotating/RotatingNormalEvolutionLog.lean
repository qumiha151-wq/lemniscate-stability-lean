import SolitonClassification.Rotating.RotatingNormalEvolutionField
import SolitonClassification.Rotating.RotatingNormalHigher

/-! The actual smooth reparameterized rotating/dilating curve in logarithmic
time. This file proves periodicity, immersion and its exact time velocity.
Identification with the evolving intrinsic elastic force is subsequent. -/
namespace SolitonClassification.Rotating.NormalEvolution
noncomputable section
open Set Real
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

variable (a : State) (L : ℝ) (h : IsClosedRotatingProfile a L)

def normalParameter (τ s : ℝ) : ℝ := scalarFlow (rotatingReparamField a L h) τ s

def normalLogX (τ s : ℝ) : ℝ := exp τ*(cos (a 4*τ)*rotatingX a (normalParameter a L h τ s)-
  sin (a 4*τ)*rotatingY a (normalParameter a L h τ s))
def normalLogY (τ s : ℝ) : ℝ := exp τ*(sin (a 4*τ)*rotatingX a (normalParameter a L h τ s)+
  cos (a 4*τ)*rotatingY a (normalParameter a L h τ s))

def rotatedTangentX (τ s : ℝ) : ℝ :=
  cos (a 4*τ)*deriv (rotatingX a) s-sin (a 4*τ)*deriv (rotatingY a) s
def rotatedTangentY (τ s : ℝ) : ℝ :=
  sin (a 4*τ)*deriv (rotatingX a) s+cos (a 4*τ)*deriv (rotatingY a) s

def profileForce (s : ℝ) : ℝ := deriv (deriv (rotatingK a)) s+(rotatingK a s)^3/2

include h in
theorem profileForce_eq (s : ℝ) : profileForce a s=
    -normalSupport (rotatingX a) (rotatingY a) s-a 4*tangentSupport (rotatingX a) (rotatingY a) s :=
  h.2.2.2.2.2.2.2 s

theorem normalParameter_joint_smooth :
    ContDiff ℝ ∞ (fun z : ℝ×ℝ => normalParameter a L h z.1 z.2) :=
  scalarFlow_joint_smooth _

theorem normalLogX_joint_smooth : ContDiff ℝ ∞ (fun z : ℝ×ℝ => normalLogX a L h z.1 z.2) := by
  exact contDiff_fst.exp.mul (((contDiff_const.mul contDiff_fst).cos.mul
    (h.2.1.comp (normalParameter_joint_smooth a L h))).sub
    ((contDiff_const.mul contDiff_fst).sin.mul (h.2.2.1.comp (normalParameter_joint_smooth a L h))))

theorem normalLogY_joint_smooth : ContDiff ℝ ∞ (fun z : ℝ×ℝ => normalLogY a L h z.1 z.2) := by
  exact contDiff_fst.exp.mul (((contDiff_const.mul contDiff_fst).sin.mul
    (h.2.1.comp (normalParameter_joint_smooth a L h))).add
    ((contDiff_const.mul contDiff_fst).cos.mul (h.2.2.1.comp (normalParameter_joint_smooth a L h))))

theorem normalParameter_period_add (τ s : ℝ) :
    normalParameter a L h τ (s+L)=normalParameter a L h τ s+L :=
  scalarFlow_period_add _ τ s

theorem normalLogX_periodic (τ : ℝ) : Function.Periodic (normalLogX a L h τ) L := by
  intro s
  simp only [normalLogX,normalParameter_period_add]
  rw [h.2.2.2.1 _,h.2.2.2.2.1 _]

theorem normalLogY_periodic (τ : ℝ) : Function.Periodic (normalLogY a L h τ) L := by
  intro s
  simp only [normalLogY,normalParameter_period_add]
  rw [h.2.2.2.1 _,h.2.2.2.2.1 _]

theorem normalLogX_initial (s : ℝ) : normalLogX a L h 0 s=rotatingX a s := by
  simp [normalLogX,normalParameter,scalarFlow_zero]
theorem normalLogY_initial (s : ℝ) : normalLogY a L h 0 s=rotatingY a s := by
  simp [normalLogY,normalParameter,scalarFlow_zero]

theorem normalLogX_spatial_derivative (τ s : ℝ) :
    HasDerivAt (normalLogX a L h τ)
      (exp τ*scalarJacobian (rotatingReparamField a L h) τ s*
        rotatedTangentX a τ (normalParameter a L h τ s)) s := by
  have hx := ((h.2.1.differentiable (by simp)) _).hasDerivAt.scomp s
    (scalarFlow_hasDerivAt_initial (rotatingReparamField a L h) τ s)
  have hy := ((h.2.2.1.differentiable (by simp)) _).hasDerivAt.scomp s
    (scalarFlow_hasDerivAt_initial (rotatingReparamField a L h) τ s)
  convert! ((hx.const_mul (cos (a 4*τ))).sub (hy.const_mul (sin (a 4*τ)))).const_mul (exp τ) using 1
  dsimp [rotatedTangentX,normalParameter]
  ring

theorem normalLogY_spatial_derivative (τ s : ℝ) :
    HasDerivAt (normalLogY a L h τ)
      (exp τ*scalarJacobian (rotatingReparamField a L h) τ s*
        rotatedTangentY a τ (normalParameter a L h τ s)) s := by
  have hx := ((h.2.1.differentiable (by simp)) _).hasDerivAt.scomp s
    (scalarFlow_hasDerivAt_initial (rotatingReparamField a L h) τ s)
  have hy := ((h.2.2.1.differentiable (by simp)) _).hasDerivAt.scomp s
    (scalarFlow_hasDerivAt_initial (rotatingReparamField a L h) τ s)
  convert! ((hx.const_mul (sin (a 4*τ))).add (hy.const_mul (cos (a 4*τ)))).const_mul (exp τ) using 1
  dsimp [rotatedTangentY,normalParameter]
  ring

include h in
theorem rotatedTangent_unit (τ s : ℝ) : rotatedTangentX a τ s^2+rotatedTangentY a τ s^2=1 := by
  have hu := h.2.2.2.2.2.1 s
  have ht := sin_sq_add_cos_sq (a 4*τ)
  calc
    _ = (sin (a 4*τ)^2+cos (a 4*τ)^2)*
      (deriv (rotatingX a) s^2+deriv (rotatingY a) s^2) := by dsimp [rotatedTangentX,rotatedTangentY]; ring
    _ = 1 := by rw [hu,ht]; ring

theorem normalLog_metric (τ s : ℝ) :
    deriv (normalLogX a L h τ) s^2+deriv (normalLogY a L h τ) s^2=
      (exp τ*scalarJacobian (rotatingReparamField a L h) τ s)^2 := by
  rw [(normalLogX_spatial_derivative a L h τ s).deriv,(normalLogY_spatial_derivative a L h τ s).deriv]
  calc
    _ = (exp τ*scalarJacobian (rotatingReparamField a L h) τ s)^2*
      (rotatedTangentX a τ (normalParameter a L h τ s)^2+
        rotatedTangentY a τ (normalParameter a L h τ s)^2) := by ring
    _ = _ := by rw [rotatedTangent_unit a L h,mul_one]

theorem normalLog_immersion (τ s : ℝ) :
    0<deriv (normalLogX a L h τ) s^2+deriv (normalLogY a L h τ) s^2 := by
  rw [normalLog_metric]
  exact sq_pos_of_pos (mul_pos (exp_pos _) (scalarJacobian_pos _ _ _))

theorem normalLogX_time_derivative (τ s : ℝ) :
    HasDerivAt (fun u => normalLogX a L h u s)
      (exp τ*profileForce a (normalParameter a L h τ s)*
        rotatedTangentY a τ (normalParameter a L h τ s)) τ := by
  let z := normalParameter a L h τ s
  let g := rotatingReparamField a L h
  have hx := ((h.2.1.differentiable (by simp)) _).hasDerivAt.scomp τ (scalarFlow_hasDerivAt g s τ)
  have hy := ((h.2.2.1.differentiable (by simp)) _).hasDerivAt.scomp τ (scalarFlow_hasDerivAt g s τ)
  have hb := (hasDerivAt_id τ).const_mul (a 4)
  have hd := (hasDerivAt_exp τ).mul ((hb.cos.mul hx).sub (hb.sin.mul hy))
  have hax := normal_velocity_algebra_x (a 4) (rotatingX a z) (rotatingY a z)
    (deriv (rotatingX a) z) (deriv (rotatingY a) z) (h.2.2.2.2.2.1 z)
  have hay := normal_velocity_algebra_y (a 4) (rotatingX a z) (rotatingY a z)
    (deriv (rotatingX a) z) (deriv (rotatingY a) z) (h.2.2.2.2.2.1 z)
  convert! hd using 1
  change exp τ*profileForce a z*rotatedTangentY a τ z=_
  rw [profileForce_eq a L h]
  dsimp [rotatedTangentY,normalSupport,tangentSupport,g,rotatingReparamField,profileReparamField,
    reparamVelocity,normalParameter,z] at hax hay ⊢
  linear_combination -(exp τ*cos (a 4*τ))*hax+(exp τ*sin (a 4*τ))*hay

theorem normalLogY_time_derivative (τ s : ℝ) :
    HasDerivAt (fun u => normalLogY a L h u s)
      (-exp τ*profileForce a (normalParameter a L h τ s)*
        rotatedTangentX a τ (normalParameter a L h τ s)) τ := by
  let z := normalParameter a L h τ s
  let g := rotatingReparamField a L h
  have hx := ((h.2.1.differentiable (by simp)) _).hasDerivAt.scomp τ (scalarFlow_hasDerivAt g s τ)
  have hy := ((h.2.2.1.differentiable (by simp)) _).hasDerivAt.scomp τ (scalarFlow_hasDerivAt g s τ)
  have hb := (hasDerivAt_id τ).const_mul (a 4)
  have hd := (hasDerivAt_exp τ).mul ((hb.sin.mul hx).add (hb.cos.mul hy))
  have hax := normal_velocity_algebra_x (a 4) (rotatingX a z) (rotatingY a z)
    (deriv (rotatingX a) z) (deriv (rotatingY a) z) (h.2.2.2.2.2.1 z)
  have hay := normal_velocity_algebra_y (a 4) (rotatingX a z) (rotatingY a z)
    (deriv (rotatingX a) z) (deriv (rotatingY a) z) (h.2.2.2.2.2.1 z)
  convert! hd using 1
  change -exp τ*profileForce a z*rotatedTangentX a τ z=_
  rw [profileForce_eq a L h]
  dsimp [rotatedTangentX,normalSupport,tangentSupport,g,rotatingReparamField,profileReparamField,
    reparamVelocity,normalParameter,z] at hax hay ⊢
  linear_combination -(exp τ*sin (a 4*τ))*hax-(exp τ*cos (a 4*τ))*hay

end
end SolitonClassification.Rotating.NormalEvolution

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name || (`ClosedSimilarity).isPrefixOf name then
      for ax in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Reparameterized actual curve audit failed: {name} depends on {ax}"
      count := count+1
  logInfo m!"Actual logarithmic-time curve audited: {count} declarations; standard axioms only."
