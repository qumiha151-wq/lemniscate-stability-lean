import SolitonClassification.Rotating.IntegerPhysicalLog

namespace SolitonClassification.Rotating.IntegerTarget.Physical
noncomputable section
open Set Real MeasureTheory NormalEvolution
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

variable (P : Seed)

theorem normalLog_speed_eq (τ s : ℝ) :
    curveSpeed (normalLogX P τ) (normalLogY P τ) s=
      exp τ*scalarJacobian (physicalField P) τ s := by
  rw [curveSpeed,normalLog_metric,Real.sqrt_sq]
  exact (mul_pos (exp_pos _) (scalarJacobian_pos _ _ _)).le

theorem normalLog_speed_pos (τ s : ℝ) :
    0<curveSpeed (normalLogX P τ) (normalLogY P τ) s := by
  rw [normalLog_speed_eq]
  exact mul_pos (exp_pos _) (scalarJacobian_pos _ _ _)

theorem normalLog_normalX (τ s : ℝ) :
    unitNormalX (normalLogX P τ) (normalLogY P τ) s=
      -rotatedTangentY P τ (normalParameter P τ s) := by
  rw [unitNormalX,normalLog_speed_eq,(normalLogY_spatial_derivative P τ s).deriv]
  field_simp [(exp_pos τ).ne',(scalarJacobian_pos (physicalField P) τ s).ne']

theorem normalLog_normalY (τ s : ℝ) :
    unitNormalY (normalLogX P τ) (normalLogY P τ) s=
      rotatedTangentX P τ (normalParameter P τ s) := by
  rw [unitNormalY,normalLog_speed_eq,(normalLogX_spatial_derivative P τ s).deriv]
  field_simp [(exp_pos τ).ne',(scalarJacobian_pos (physicalField P) τ s).ne']

theorem rotatingK_smooth_of_closed_profile : ContDiff ℝ ∞ (P.I.k) := by
  have he : P.I.k=fun s => deriv (P.I.x) s*deriv (deriv (P.I.y)) s-
      deriv (P.I.y) s*deriv (deriv (P.I.x)) s :=
    funext fun s => (P.I.curvature s).symm
  rw [he]
  exact (P.I.smoothX.deriv'.mul P.I.smoothY.deriv'.deriv').sub (P.I.smoothY.deriv'.mul P.I.smoothX.deriv'.deriv')

theorem rotatedTangentX_hasDerivAt (τ s : ℝ) :
    HasDerivAt (rotatedTangentX P τ)
      (cos (P.b*τ)*deriv (deriv (P.I.x)) s-
        sin (P.b*τ)*deriv (deriv (P.I.y)) s) s := by
  have hx : ContDiff ℝ ∞ (deriv (P.I.x)) := P.I.smoothX.deriv'
  have hy : ContDiff ℝ ∞ (deriv (P.I.y)) := P.I.smoothY.deriv'
  exact (((hx.differentiable (by simp)) s).hasDerivAt.const_mul _).sub
    (((hy.differentiable (by simp)) s).hasDerivAt.const_mul _)

theorem rotatedTangentY_hasDerivAt (τ s : ℝ) :
    HasDerivAt (rotatedTangentY P τ)
      (sin (P.b*τ)*deriv (deriv (P.I.x)) s+
        cos (P.b*τ)*deriv (deriv (P.I.y)) s) s := by
  have hx : ContDiff ℝ ∞ (deriv (P.I.x)) := P.I.smoothX.deriv'
  have hy : ContDiff ℝ ∞ (deriv (P.I.y)) := P.I.smoothY.deriv'
  exact (((hx.differentiable (by simp)) s).hasDerivAt.const_mul _).add
    (((hy.differentiable (by simp)) s).hasDerivAt.const_mul _)

theorem rotatedTangent_curvature (τ s : ℝ) :
    rotatedTangentX P τ s*deriv (rotatedTangentY P τ) s-
      rotatedTangentY P τ s*deriv (rotatedTangentX P τ) s=P.I.k s := by
  rw [(rotatedTangentX_hasDerivAt P τ s).deriv,
    (rotatedTangentY_hasDerivAt P τ s).deriv]
  calc
    _ = (sin (P.b*τ)^2+cos (P.b*τ)^2)*
      (deriv (P.I.x) s*deriv (deriv (P.I.y)) s-
        deriv (P.I.y) s*deriv (deriv (P.I.x)) s) := by
      dsimp [rotatedTangentX,rotatedTangentY]
      ring
    _ = P.I.k s := by rw [sin_sq_add_cos_sq,P.I.curvature,one_mul]

theorem normalLog_determinant (τ s : ℝ) :
    deriv (normalLogX P τ) s*deriv (deriv (normalLogY P τ)) s-
      deriv (normalLogY P τ) s*deriv (deriv (normalLogX P τ)) s=
      exp τ^2*(scalarJacobian (physicalField P) τ s)^3*
        P.I.k (normalParameter P τ s) := by
  let g := physicalField P
  let J := scalarJacobian g τ
  let φ := normalParameter P τ
  have hJ : HasDerivAt J (deriv J s) s :=
    ((scalarJacobian_spatial_smooth g τ).differentiable (by simp) s).hasDerivAt
  have hφ : HasDerivAt φ (J s) s := scalarFlow_hasDerivAt_initial g τ s
  have hx : deriv (normalLogX P τ)=fun u => exp τ*J u*rotatedTangentX P τ (φ u) :=
    funext fun u => (normalLogX_spatial_derivative P τ u).deriv
  have hy : deriv (normalLogY P τ)=fun u => exp τ*J u*rotatedTangentY P τ (φ u) :=
    funext fun u => (normalLogY_spatial_derivative P τ u).deriv
  have htx := rotatedTangentX_hasDerivAt P τ (φ s)
  have hty := rotatedTangentY_hasDerivAt P τ (φ s)
  have htx' : HasDerivAt (rotatedTangentX P τ) (deriv (rotatedTangentX P τ) (φ s)) (φ s) :=
    htx.differentiableAt.hasDerivAt
  have hty' : HasDerivAt (rotatedTangentY P τ) (deriv (rotatedTangentY P τ) (φ s)) (φ s) :=
    hty.differentiableAt.hasDerivAt
  have hxx := (hJ.const_mul (exp τ)).mul (htx'.comp s hφ)
  have hyy := (hJ.const_mul (exp τ)).mul (hty'.comp s hφ)
  change HasDerivAt (fun u => exp τ*J u*rotatedTangentX P τ (φ u))
    (exp τ*deriv J s*rotatedTangentX P τ (φ s)+
      exp τ*J s*(deriv (rotatedTangentX P τ) (φ s)*J s)) s at hxx
  change HasDerivAt (fun u => exp τ*J u*rotatedTangentY P τ (φ u))
    (exp τ*deriv J s*rotatedTangentY P τ (φ s)+
      exp τ*J s*(deriv (rotatedTangentY P τ) (φ s)*J s)) s at hyy
  rw [hx,hy,hxx.deriv,hyy.deriv]
  change _=exp τ^2*(J s)^3*P.I.k (φ s)
  calc
    _ = exp τ^2*(J s)^3*(rotatedTangentX P τ (φ s)*deriv (rotatedTangentY P τ) (φ s)-
      rotatedTangentY P τ (φ s)*deriv (rotatedTangentX P τ) (φ s)) := by ring
    _ = _ := by rw [rotatedTangent_curvature P]

theorem normalLog_curvature (τ s : ℝ) :
    intrinsicCurvature (normalLogX P τ) (normalLogY P τ) s=
      exp (-τ)*P.I.k (normalParameter P τ s) := by
  rw [intrinsicCurvature,normalLog_determinant,normalLog_speed_eq,exp_neg]
  field_simp [(exp_pos τ).ne',(scalarJacobian_pos (physicalField P) τ s).ne']

theorem normalLog_arc_chain {f : ℝ → ℝ} {f' τ s : ℝ} (c : ℝ)
    (hf : HasDerivAt f f' (normalParameter P τ s)) :
    arcDerivative (normalLogX P τ) (normalLogY P τ)
      (fun u => c*f (normalParameter P τ u)) s=c*exp (-τ)*f' := by
  have hd := (hf.comp s (scalarFlow_hasDerivAt_initial (physicalField P) τ s)).const_mul c
  change HasDerivAt (fun u => c*f (normalParameter P τ u))
    (c*(f'*scalarJacobian (physicalField P) τ s)) s at hd
  rw [arcDerivative,normalLog_speed_eq,hd.deriv,exp_neg]
  field_simp [(exp_pos τ).ne',(scalarJacobian_pos (physicalField P) τ s).ne']

theorem normalLog_curvature_first (τ s : ℝ) :
    arcDerivative (normalLogX P τ) (normalLogY P τ)
      (intrinsicCurvature (normalLogX P τ) (normalLogY P τ)) s=
      exp (-τ)^2*deriv (P.I.k) (normalParameter P τ s) := by
  have hk := (rotatingK_smooth_of_closed_profile P).differentiable (by simp)
  rw [show intrinsicCurvature (normalLogX P τ) (normalLogY P τ)=
    fun u => exp (-τ)*P.I.k (normalParameter P τ u) from
    funext (normalLog_curvature P τ)]
  rw [normalLog_arc_chain P _ (hk _).hasDerivAt]
  ring

theorem normalLog_curvature_second (τ s : ℝ) :
    arcDerivative (normalLogX P τ) (normalLogY P τ)
      (arcDerivative (normalLogX P τ) (normalLogY P τ)
        (intrinsicCurvature (normalLogX P τ) (normalLogY P τ))) s=
      exp (-τ)^3*deriv (deriv (P.I.k)) (normalParameter P τ s) := by
  have hkd : ContDiff ℝ ∞ (deriv (P.I.k)) := (rotatingK_smooth_of_closed_profile P).deriv'
  have hk := hkd.differentiable (by simp)
  rw [show arcDerivative (normalLogX P τ) (normalLogY P τ)
      (intrinsicCurvature (normalLogX P τ) (normalLogY P τ))=
    fun u => exp (-τ)^2*deriv (P.I.k) (normalParameter P τ u) from
    funext (normalLog_curvature_first P τ)]
  rw [normalLog_arc_chain P _ (hk _).hasDerivAt]
  ring

theorem normalLog_force (τ s : ℝ) :
    intrinsicElasticForce (normalLogX P τ) (normalLogY P τ) s=
      exp (-3*τ)*profileForce P (normalParameter P τ s) := by
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
end SolitonClassification.Rotating.IntegerTarget.Physical
#print axioms SolitonClassification.Rotating.IntegerTarget.Physical.normalLog_force
