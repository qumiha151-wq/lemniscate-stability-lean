import SolitonClassification.Rotating.IntegerPhysicalTime

namespace SolitonClassification.Rotating.IntegerTarget.Physical
noncomputable section
open Set Real MeasureTheory NormalEvolution
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

variable (P : Seed)

theorem normal_speed_eq (t s : ℝ) : curveSpeed (normalX P t) (normalY P t) s=
    dilationScale t*scalarJacobian (physicalField P) (logClock t) s :=
  normalLog_speed_eq P (logClock t) s

theorem normal_speed_pos (t s : ℝ) : 0<curveSpeed (normalX P t) (normalY P t) s :=
  normalLog_speed_pos P (logClock t) s

theorem normal_curvature (t s : ℝ) : intrinsicCurvature (normalX P t) (normalY P t) s=
    exp (-logClock t)*P.I.k (normalParameter P (logClock t) s) :=
  normalLog_curvature P (logClock t) s

theorem normal_force (t s : ℝ) : intrinsicElasticForce (normalX P t) (normalY P t) s=
    exp (-3*logClock t)*profileForce P (normalParameter P (logClock t) s) :=
  normalLog_force P (logClock t) s

theorem normal_unitNormalX (t s : ℝ) : unitNormalX (normalX P t) (normalY P t) s=
    -rotatedTangentY P (logClock t) (normalParameter P (logClock t) s) :=
  normalLog_normalX P (logClock t) s

theorem normal_unitNormalY (t s : ℝ) : unitNormalY (normalX P t) (normalY P t) s=
    rotatedTangentX P (logClock t) (normalParameter P (logClock t) s) :=
  normalLog_normalY P (logClock t) s

theorem normalX_free_elastic {t : ℝ} (ht : -1/4<t) (s : ℝ) :
    HasDerivAt (fun u => normalX P u s)
      (-intrinsicElasticForce (normalX P t) (normalY P t) s*
        unitNormalX (normalX P t) (normalY P t) s) t := by
  convert! normalX_time_derivative P ht s using 1
  rw [normal_force,normal_unitNormalX]
  ring

theorem normalY_free_elastic {t : ℝ} (ht : -1/4<t) (s : ℝ) :
    HasDerivAt (fun u => normalY P u s)
      (-intrinsicElasticForce (normalX P t) (normalY P t) s*
        unitNormalY (normalX P t) (normalY P t) s) t := by
  convert! normalY_time_derivative P ht s using 1
  rw [normal_force,normal_unitNormalY]
  ring

theorem normalEvolution_is_pure_normal :
    IsPureNormalElasticEvolution P.L (normalX P) (normalY P) where
  period_pos := P.positive
  smooth_X := normalX_joint_smooth P
  smooth_Y := normalY_joint_smooth P
  closed_X := fun t _ => normalX_periodic P t
  closed_Y := fun t _ => normalY_periodic P t
  regular := fun t _ => normal_speed_pos P t
  evolution_X := fun _ ht => normalX_free_elastic P ht
  evolution_Y := fun _ ht => normalY_free_elastic P ht

theorem normal_length (t : ℝ) :
    (∫s in 0..P.L,curveSpeed (normalX P t) (normalY P t) s)=dilationScale t*P.L := by
  simp_rw [normal_speed_eq]
  rw [intervalIntegral.integral_const_mul]
  have hi := scalarFlow_jacobian_integral (physicalField P) (logClock t)
  change (∫s in 0..P.L,scalarJacobian (physicalField P) (logClock t) s)=P.L at hi
  rw [hi]

theorem normalEvolution_future (t : ℝ) (ht : 0≤t) (s : ℝ) :
    HasDerivAt (fun u => normalX P u s)
      (-intrinsicElasticForce (normalX P t) (normalY P t) s*
        unitNormalX (normalX P t) (normalY P t) s) t ∧
    HasDerivAt (fun u => normalY P u s)
      (-intrinsicElasticForce (normalX P t) (normalY P t) s*
        unitNormalY (normalX P t) (normalY P t) s) t :=
  ⟨normalX_free_elastic P (by linarith) s,normalY_free_elastic P (by linarith) s⟩


end
end SolitonClassification.Rotating.IntegerTarget.Physical
#print axioms SolitonClassification.Rotating.IntegerTarget.Physical.normalEvolution_is_pure_normal
