import SolitonClassification.Rotating.RotatingNormalEvolutionLog

/-! Intrinsic quantities are computed from the actual coordinate derivatives.
The speed, signed curvature and twice-arclength differentiated curvature are
identified with their similarity-scaled profile expressions. -/
namespace SolitonClassification.Rotating.NormalEvolution
noncomputable section
open Set Real
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

def curveSpeed (X Y : ℝ → ℝ) (s : ℝ) : ℝ :=
  sqrt ((deriv X s)^2+(deriv Y s)^2)

def arcDerivative (X Y f : ℝ → ℝ) (s : ℝ) : ℝ := deriv f s/curveSpeed X Y s

def unitNormalX (X Y : ℝ → ℝ) (s : ℝ) : ℝ := -deriv Y s/curveSpeed X Y s
def unitNormalY (X Y : ℝ → ℝ) (s : ℝ) : ℝ := deriv X s/curveSpeed X Y s

def intrinsicCurvature (X Y : ℝ → ℝ) (s : ℝ) : ℝ :=
  (deriv X s*deriv (deriv Y) s-deriv Y s*deriv (deriv X) s)/(curveSpeed X Y s)^3

def intrinsicElasticForce (X Y : ℝ → ℝ) (s : ℝ) : ℝ :=
  arcDerivative X Y (arcDerivative X Y (intrinsicCurvature X Y)) s+
    (intrinsicCurvature X Y s)^3/2

variable (a : State) (L : ℝ) (h : IsClosedRotatingProfile a L)

theorem normalLog_speed_eq (τ s : ℝ) :
    curveSpeed (normalLogX a L h τ) (normalLogY a L h τ) s=
      exp τ*scalarJacobian (rotatingReparamField a L h) τ s := by
  rw [curveSpeed,normalLog_metric,Real.sqrt_sq]
  exact (mul_pos (exp_pos _) (scalarJacobian_pos _ _ _)).le

theorem normalLog_speed_pos (τ s : ℝ) :
    0<curveSpeed (normalLogX a L h τ) (normalLogY a L h τ) s := by
  rw [normalLog_speed_eq]
  exact mul_pos (exp_pos _) (scalarJacobian_pos _ _ _)

theorem normalLog_normalX (τ s : ℝ) :
    unitNormalX (normalLogX a L h τ) (normalLogY a L h τ) s=
      -rotatedTangentY a τ (normalParameter a L h τ s) := by
  rw [unitNormalX,normalLog_speed_eq,(normalLogY_spatial_derivative a L h τ s).deriv]
  field_simp [(exp_pos τ).ne',(scalarJacobian_pos (rotatingReparamField a L h) τ s).ne']

theorem normalLog_normalY (τ s : ℝ) :
    unitNormalY (normalLogX a L h τ) (normalLogY a L h τ) s=
      rotatedTangentX a τ (normalParameter a L h τ s) := by
  rw [unitNormalY,normalLog_speed_eq,(normalLogX_spatial_derivative a L h τ s).deriv]
  field_simp [(exp_pos τ).ne',(scalarJacobian_pos (rotatingReparamField a L h) τ s).ne']

include h in
theorem rotatingK_smooth_of_closed_profile : ContDiff ℝ ∞ (rotatingK a) := by
  have he : rotatingK a=fun s => deriv (rotatingX a) s*deriv (deriv (rotatingY a)) s-
      deriv (rotatingY a) s*deriv (deriv (rotatingX a)) s :=
    funext fun s => (h.2.2.2.2.2.2.1 s).symm
  rw [he]
  exact (h.2.1.deriv'.mul h.2.2.1.deriv'.deriv').sub (h.2.2.1.deriv'.mul h.2.1.deriv'.deriv')

theorem scalarJacobian_spatial_smooth (g : PeriodicScalarField) (τ : ℝ) :
    ContDiff ℝ ∞ (scalarJacobian g τ) := by
  have he : scalarJacobian g τ=deriv (scalarFlow g τ) :=
    funext fun s => (scalarFlow_hasDerivAt_initial g τ s).deriv.symm
  rw [he]
  exact (scalarFlow_spatial_smooth g τ).deriv'

include h in
theorem rotatedTangentX_hasDerivAt (τ s : ℝ) :
    HasDerivAt (rotatedTangentX a τ)
      (cos (a 4*τ)*deriv (deriv (rotatingX a)) s-
        sin (a 4*τ)*deriv (deriv (rotatingY a)) s) s := by
  have hx : ContDiff ℝ ∞ (deriv (rotatingX a)) := h.2.1.deriv'
  have hy : ContDiff ℝ ∞ (deriv (rotatingY a)) := h.2.2.1.deriv'
  exact (((hx.differentiable (by simp)) s).hasDerivAt.const_mul _).sub
    (((hy.differentiable (by simp)) s).hasDerivAt.const_mul _)

include h in
theorem rotatedTangentY_hasDerivAt (τ s : ℝ) :
    HasDerivAt (rotatedTangentY a τ)
      (sin (a 4*τ)*deriv (deriv (rotatingX a)) s+
        cos (a 4*τ)*deriv (deriv (rotatingY a)) s) s := by
  have hx : ContDiff ℝ ∞ (deriv (rotatingX a)) := h.2.1.deriv'
  have hy : ContDiff ℝ ∞ (deriv (rotatingY a)) := h.2.2.1.deriv'
  exact (((hx.differentiable (by simp)) s).hasDerivAt.const_mul _).add
    (((hy.differentiable (by simp)) s).hasDerivAt.const_mul _)

include h in
theorem rotatedTangent_curvature (τ s : ℝ) :
    rotatedTangentX a τ s*deriv (rotatedTangentY a τ) s-
      rotatedTangentY a τ s*deriv (rotatedTangentX a τ) s=rotatingK a s := by
  rw [(rotatedTangentX_hasDerivAt a L h τ s).deriv,
    (rotatedTangentY_hasDerivAt a L h τ s).deriv]
  calc
    _ = (sin (a 4*τ)^2+cos (a 4*τ)^2)*
      (deriv (rotatingX a) s*deriv (deriv (rotatingY a)) s-
        deriv (rotatingY a) s*deriv (deriv (rotatingX a)) s) := by
      dsimp [rotatedTangentX,rotatedTangentY]
      ring
    _ = rotatingK a s := by rw [sin_sq_add_cos_sq,h.2.2.2.2.2.2.1,one_mul]

theorem normalLog_determinant (τ s : ℝ) :
    deriv (normalLogX a L h τ) s*deriv (deriv (normalLogY a L h τ)) s-
      deriv (normalLogY a L h τ) s*deriv (deriv (normalLogX a L h τ)) s=
      exp τ^2*(scalarJacobian (rotatingReparamField a L h) τ s)^3*
        rotatingK a (normalParameter a L h τ s) := by
  let g := rotatingReparamField a L h
  let J := scalarJacobian g τ
  let φ := normalParameter a L h τ
  have hJ : HasDerivAt J (deriv J s) s :=
    ((scalarJacobian_spatial_smooth g τ).differentiable (by simp) s).hasDerivAt
  have hφ : HasDerivAt φ (J s) s := scalarFlow_hasDerivAt_initial g τ s
  have hx : deriv (normalLogX a L h τ)=fun u => exp τ*J u*rotatedTangentX a τ (φ u) :=
    funext fun u => (normalLogX_spatial_derivative a L h τ u).deriv
  have hy : deriv (normalLogY a L h τ)=fun u => exp τ*J u*rotatedTangentY a τ (φ u) :=
    funext fun u => (normalLogY_spatial_derivative a L h τ u).deriv
  have htx := rotatedTangentX_hasDerivAt a L h τ (φ s)
  have hty := rotatedTangentY_hasDerivAt a L h τ (φ s)
  have htx' : HasDerivAt (rotatedTangentX a τ) (deriv (rotatedTangentX a τ) (φ s)) (φ s) :=
    htx.differentiableAt.hasDerivAt
  have hty' : HasDerivAt (rotatedTangentY a τ) (deriv (rotatedTangentY a τ) (φ s)) (φ s) :=
    hty.differentiableAt.hasDerivAt
  have hxx := (hJ.const_mul (exp τ)).mul (htx'.comp s hφ)
  have hyy := (hJ.const_mul (exp τ)).mul (hty'.comp s hφ)
  change HasDerivAt (fun u => exp τ*J u*rotatedTangentX a τ (φ u))
    (exp τ*deriv J s*rotatedTangentX a τ (φ s)+
      exp τ*J s*(deriv (rotatedTangentX a τ) (φ s)*J s)) s at hxx
  change HasDerivAt (fun u => exp τ*J u*rotatedTangentY a τ (φ u))
    (exp τ*deriv J s*rotatedTangentY a τ (φ s)+
      exp τ*J s*(deriv (rotatedTangentY a τ) (φ s)*J s)) s at hyy
  rw [hx,hy,hxx.deriv,hyy.deriv]
  change _=exp τ^2*(J s)^3*rotatingK a (φ s)
  calc
    _ = exp τ^2*(J s)^3*(rotatedTangentX a τ (φ s)*deriv (rotatedTangentY a τ) (φ s)-
      rotatedTangentY a τ (φ s)*deriv (rotatedTangentX a τ) (φ s)) := by ring
    _ = _ := by rw [rotatedTangent_curvature a L h]

theorem normalLog_curvature (τ s : ℝ) :
    intrinsicCurvature (normalLogX a L h τ) (normalLogY a L h τ) s=
      exp (-τ)*rotatingK a (normalParameter a L h τ s) := by
  rw [intrinsicCurvature,normalLog_determinant,normalLog_speed_eq,exp_neg]
  field_simp [(exp_pos τ).ne',(scalarJacobian_pos (rotatingReparamField a L h) τ s).ne']

theorem normalLog_arc_chain {f : ℝ → ℝ} {f' τ s : ℝ} (c : ℝ)
    (hf : HasDerivAt f f' (normalParameter a L h τ s)) :
    arcDerivative (normalLogX a L h τ) (normalLogY a L h τ)
      (fun u => c*f (normalParameter a L h τ u)) s=c*exp (-τ)*f' := by
  have hd := (hf.comp s (scalarFlow_hasDerivAt_initial (rotatingReparamField a L h) τ s)).const_mul c
  change HasDerivAt (fun u => c*f (normalParameter a L h τ u))
    (c*(f'*scalarJacobian (rotatingReparamField a L h) τ s)) s at hd
  rw [arcDerivative,normalLog_speed_eq,hd.deriv,exp_neg]
  field_simp [(exp_pos τ).ne',(scalarJacobian_pos (rotatingReparamField a L h) τ s).ne']

theorem normalLog_curvature_first (τ s : ℝ) :
    arcDerivative (normalLogX a L h τ) (normalLogY a L h τ)
      (intrinsicCurvature (normalLogX a L h τ) (normalLogY a L h τ)) s=
      exp (-τ)^2*deriv (rotatingK a) (normalParameter a L h τ s) := by
  have hk := (rotatingK_smooth_of_closed_profile a L h).differentiable (by simp)
  rw [show intrinsicCurvature (normalLogX a L h τ) (normalLogY a L h τ)=
    fun u => exp (-τ)*rotatingK a (normalParameter a L h τ u) from
    funext (normalLog_curvature a L h τ)]
  rw [normalLog_arc_chain a L h _ (hk _).hasDerivAt]
  ring

theorem normalLog_curvature_second (τ s : ℝ) :
    arcDerivative (normalLogX a L h τ) (normalLogY a L h τ)
      (arcDerivative (normalLogX a L h τ) (normalLogY a L h τ)
        (intrinsicCurvature (normalLogX a L h τ) (normalLogY a L h τ))) s=
      exp (-τ)^3*deriv (deriv (rotatingK a)) (normalParameter a L h τ s) := by
  have hkd : ContDiff ℝ ∞ (deriv (rotatingK a)) := (rotatingK_smooth_of_closed_profile a L h).deriv'
  have hk := hkd.differentiable (by simp)
  rw [show arcDerivative (normalLogX a L h τ) (normalLogY a L h τ)
      (intrinsicCurvature (normalLogX a L h τ) (normalLogY a L h τ))=
    fun u => exp (-τ)^2*deriv (rotatingK a) (normalParameter a L h τ u) from
    funext (normalLog_curvature_first a L h τ)]
  rw [normalLog_arc_chain a L h _ (hk _).hasDerivAt]
  ring

theorem normalLog_force (τ s : ℝ) :
    intrinsicElasticForce (normalLogX a L h τ) (normalLogY a L h τ) s=
      exp (-3*τ)*profileForce a (normalParameter a L h τ s) := by
  rw [intrinsicElasticForce,normalLog_curvature_second,normalLog_curvature]
  have he : exp (-τ)^3=exp (-3*τ) := by
    calc
      _ = exp (-τ)*exp (-τ)*exp (-τ) := by ring
      _ = exp (-τ+-τ+-τ) := by rw [exp_add,exp_add]
      _ = _ := by congr 1; ring
  dsimp [profileForce]
  rw [mul_pow,he]
  ring

end
end SolitonClassification.Rotating.NormalEvolution

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name || (`ClosedSimilarity).isPrefixOf name then
      for ax in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Actual intrinsic-curvature audit failed: {name} depends on {ax}"
      count := count+1
  logInfo m!"Actual intrinsic curvature and elastic force audited: {count} declarations; standard axioms only."
