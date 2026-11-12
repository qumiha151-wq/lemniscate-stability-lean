import OpenTranslators.ParameterHigher

/-! Pure-normal free elastic flow with force computed from the actual
reparametrized curve's Euclidean speed, unit tangent and arclength derivatives.
The parameter map's joint smoothness and positive derivative are proved upstream. -/
namespace OpenTranslator.TranslatorPureNormal
noncomputable section
open MeasureTheory Set
open scoped ContDiff
open TranslatorParameter TranslatorGeometry
set_option backward.isDefEq.respectTransparency false

def curveSpeed (X Y : ℝ → ℝ) (s : ℝ) : ℝ := Real.sqrt ((deriv X s)^2+(deriv Y s)^2)
def arcDerivative (X Y f : ℝ → ℝ) (s : ℝ) : ℝ := deriv f s/curveSpeed X Y s
def unitTangentX (X Y : ℝ → ℝ) : ℝ → ℝ := arcDerivative X Y X
def unitTangentY (X Y : ℝ → ℝ) : ℝ → ℝ := arcDerivative X Y Y
def unitNormalX (X Y : ℝ → ℝ) (s : ℝ) : ℝ := -unitTangentY X Y s
def unitNormalY (X Y : ℝ → ℝ) (s : ℝ) : ℝ := unitTangentX X Y s
def intrinsicCurvature (X Y : ℝ → ℝ) (s : ℝ) : ℝ :=
  arcDerivative X Y (unitTangentX X Y) s*unitNormalX X Y s+
    arcDerivative X Y (unitTangentY X Y) s*unitNormalY X Y s
def intrinsicElasticForce (X Y : ℝ → ℝ) (s : ℝ) : ℝ :=
  arcDerivative X Y (arcDerivative X Y (intrinsicCurvature X Y)) s+
    intrinsicCurvature X Y s^3/2

variable {z : ℝ → TranslatorState}
variable (hz : ∀ s, HasDerivAt z (translatorNumerator (z s)) s)

def curveX (t u : ℝ) : ℝ := betaX z (parameterFlow hz t u)+t
def curveY (t u : ℝ) : ℝ := betaY z (parameterFlow hz t u)

theorem curve_joint_smooth :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => (curveX hz p.1 p.2,curveY hz p.1 p.2)) := by
  exact (((betaX_smooth hz).comp (parameterFlow_joint_smooth hz)).add contDiff_fst).prodMk
    ((betaY_smooth hz).comp (parameterFlow_joint_smooth hz))

theorem curve_spatial_hasDerivAt (t u : ℝ) :
    HasDerivAt (curveX hz t)
      (Real.cos (z (parameterFlow hz t u) 0)*parameterJacobian hz t u) u ∧
    HasDerivAt (curveY hz t)
      (Real.sin (z (parameterFlow hz t u) 0)*parameterJacobian hz t u) u :=
  ⟨((betaX_hasDerivAt hz (parameterFlow hz t u)).comp u
      (parameterFlow_hasDerivAt_initial hz t u)).add_const t,
    (betaY_hasDerivAt hz (parameterFlow hz t u)).comp u
      (parameterFlow_hasDerivAt_initial hz t u)⟩

theorem curve_speed_eq (t u : ℝ) :
    curveSpeed (curveX hz t) (curveY hz t) u=parameterJacobian hz t u := by
  obtain ⟨hx,hy⟩ := curve_spatial_hasDerivAt hz t u
  have he : (deriv (curveX hz t) u)^2+(deriv (curveY hz t) u)^2=(parameterJacobian hz t u)^2 := by
    rw [hx.deriv,hy.deriv]
    have hh := Real.cos_sq_add_sin_sq (z (parameterFlow hz t u) 0)
    linear_combination (parameterJacobian hz t u)^2*hh
  rw [curveSpeed,he,Real.sqrt_sq (parameterJacobian_pos hz t u).le]

theorem curve_speed_pos (t u : ℝ) : 0<curveSpeed (curveX hz t) (curveY hz t) u := by
  rw [curve_speed_eq hz]
  exact parameterJacobian_pos hz t u

theorem arc_chain {f : ℝ → ℝ} {f' t u : ℝ}
    (hf : HasDerivAt f f' (parameterFlow hz t u)) :
    arcDerivative (curveX hz t) (curveY hz t) (fun v => f (parameterFlow hz t v)) u=f' := by
  have hd := hf.comp u (parameterFlow_hasDerivAt_initial hz t u)
  change HasDerivAt (fun v => f (parameterFlow hz t v)) (f'*parameterJacobian hz t u) u at hd
  rw [arcDerivative,curve_speed_eq hz,hd.deriv,
    mul_div_cancel_right₀ _ (parameterJacobian_pos hz t u).ne']

theorem curve_tangentX (t u : ℝ) :
    unitTangentX (curveX hz t) (curveY hz t) u=Real.cos (z (parameterFlow hz t u) 0) := by
  rw [unitTangentX,arcDerivative,curve_speed_eq hz,
    (curve_spatial_hasDerivAt hz t u).1.deriv,
    mul_div_cancel_right₀ _ (parameterJacobian_pos hz t u).ne']

theorem curve_tangentY (t u : ℝ) :
    unitTangentY (curveX hz t) (curveY hz t) u=Real.sin (z (parameterFlow hz t u) 0) := by
  rw [unitTangentY,arcDerivative,curve_speed_eq hz,
    (curve_spatial_hasDerivAt hz t u).2.deriv,
    mul_div_cancel_right₀ _ (parameterJacobian_pos hz t u).ne']

theorem curve_normalX (t u : ℝ) :
    unitNormalX (curveX hz t) (curveY hz t) u= -Real.sin (z (parameterFlow hz t u) 0) := by
  rw [unitNormalX,curve_tangentY hz]

theorem curve_normalY (t u : ℝ) :
    unitNormalY (curveX hz t) (curveY hz t) u=Real.cos (z (parameterFlow hz t u) 0) := by
  rw [unitNormalY,curve_tangentX hz]

theorem curve_curvature (t u : ℝ) :
    intrinsicCurvature (curveX hz t) (curveY hz t) u=z (parameterFlow hz t u) 1 := by
  have hX : unitTangentX (curveX hz t) (curveY hz t)=
      fun v => Real.cos (z (parameterFlow hz t v) 0) := funext (curve_tangentX hz t)
  have hY : unitTangentY (curveX hz t) (curveY hz t)=
      fun v => Real.sin (z (parameterFlow hz t v) 0) := funext (curve_tangentY hz t)
  rw [intrinsicCurvature,hX,hY,curve_normalX hz,curve_normalY hz,
    arc_chain hz (theta_hasDerivAt hz (parameterFlow hz t u)).cos,
    arc_chain hz (theta_hasDerivAt hz (parameterFlow hz t u)).sin]
  have hh := Real.cos_sq_add_sin_sq (z (parameterFlow hz t u) 0)
  linear_combination z (parameterFlow hz t u) 1*hh

theorem curve_curvature_first (t u : ℝ) :
    arcDerivative (curveX hz t) (curveY hz t)
      (intrinsicCurvature (curveX hz t) (curveY hz t)) u=z (parameterFlow hz t u) 2 := by
  have hk : intrinsicCurvature (curveX hz t) (curveY hz t)=
      fun v => z (parameterFlow hz t v) 1 := funext (curve_curvature hz t)
  rw [hk]
  exact arc_chain hz (curvature_hasDerivAt hz (parameterFlow hz t u))

theorem curve_curvature_second (t u : ℝ) :
    arcDerivative (curveX hz t) (curveY hz t)
      (arcDerivative (curveX hz t) (curveY hz t)
        (intrinsicCurvature (curveX hz t) (curveY hz t))) u=
      -(z (parameterFlow hz t u) 1)^3/2+Real.sin (z (parameterFlow hz t u) 0) := by
  have hv : arcDerivative (curveX hz t) (curveY hz t)
      (intrinsicCurvature (curveX hz t) (curveY hz t))=
      fun v => z (parameterFlow hz t v) 2 := funext (curve_curvature_first hz t)
  rw [hv]
  exact arc_chain hz (curvatureDerivative_hasDerivAt hz (parameterFlow hz t u))

theorem curve_force (t u : ℝ) :
    intrinsicElasticForce (curveX hz t) (curveY hz t) u=Real.sin (z (parameterFlow hz t u) 0) := by
  rw [intrinsicElasticForce,curve_curvature_second hz,curve_curvature hz]
  ring

theorem curve_time_hasDerivAt (t u : ℝ) :
    HasDerivAt (fun r => curveX hz r u) (Real.sin (z (parameterFlow hz t u) 0)^2) t ∧
      HasDerivAt (fun r => curveY hz r u)
        (-Real.sin (z (parameterFlow hz t u) 0)*Real.cos (z (parameterFlow hz t u) 0)) t := by
  constructor
  · convert ((betaX_hasDerivAt hz (parameterFlow hz t u)).comp t
      (parameterFlow_derivative hz u t)).add (hasDerivAt_id t) using 1 <;>
      first | rfl | (simp only [parameterField]; nlinarith [Real.sin_sq_add_cos_sq (z (parameterFlow hz t u) 0)])
  · convert (betaY_hasDerivAt hz (parameterFlow hz t u)).comp t
      (parameterFlow_derivative hz u t) using 1 <;>
      first | rfl | (simp only [parameterField]; ring)

/-- The whole velocity, not merely its normal projection, equals minus the
actual intrinsic elastic force times the actual unit normal. -/
theorem curve_intrinsic_pure_normal_FEF (t u : ℝ) :
    HasDerivAt (fun r => (curveX hz r u,curveY hz r u))
      (-intrinsicElasticForce (curveX hz t) (curveY hz t) u*
          unitNormalX (curveX hz t) (curveY hz t) u,
        -intrinsicElasticForce (curveX hz t) (curveY hz t) u*
          unitNormalY (curveX hz t) (curveY hz t) u) t := by
  rw [curve_force hz,curve_normalX hz,curve_normalY hz]
  simpa only [neg_mul_neg,pow_two] using
    (curve_time_hasDerivAt hz t u).1.prodMk (curve_time_hasDerivAt hz t u).2

theorem curve_initial (u : ℝ) :
    curveX hz 0 u=betaX z u ∧ curveY hz 0 u=betaY z u := by
  simp only [curveX,curveY,parameterFlow_zero,add_zero,and_self]

def intrinsicDistance (X Y : ℝ → ℝ) (a b : ℝ) : ℝ := |∫ u in a..b, curveSpeed X Y u|

/-- The actual induced arclength distance is conjugate to the complete real
line by the proved smooth bijection, making preservation of completeness
explicit without treating the original parameter as unit speed. -/
theorem curve_intrinsicDistance (t a b : ℝ) :
    intrinsicDistance (curveX hz t) (curveY hz t) a b=
      dist (parameterFlow hz t a) (parameterFlow hz t b) := by
  have hJ : Continuous (parameterJacobian hz t) := by
    have he : deriv (parameterFlow hz t)=parameterJacobian hz t :=
      funext fun u => (parameterFlow_hasDerivAt_initial hz t u).deriv
    rw [← he]
    exact (contDiff_infty_iff_deriv.mp (parameterFlow_spatial_smooth hz t)).2.continuous
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u (_ : u∈uIcc a b) => parameterFlow_hasDerivAt_initial hz t u)
    (hJ.intervalIntegrable a b)
  rw [intrinsicDistance]
  simp only [curve_speed_eq hz]
  rw [hi,Real.dist_eq,abs_sub_comm]

end
end OpenTranslator.TranslatorPureNormal

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`OpenTranslator).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Parameter intrinsic audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Parameter intrinsic audit passed for {count} declarations."
