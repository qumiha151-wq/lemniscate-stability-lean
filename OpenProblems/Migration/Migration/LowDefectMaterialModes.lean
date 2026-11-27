import Migration.LowDefectTangentMoments
import Migration.LowDefectVirial

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.PeriodicRegularPosition
variable (p : PeriodicRegularPosition)

def fractionalTangent (x : ℝ) : ℂ :=
  tangent p.position (p.arclengthInverse (p.length*x))
def fractionalCurvature (x : ℝ) : ℝ :=
  p.length * curvature p.position (p.arclengthInverse (p.length*x))

theorem fractionalTangent_hasDerivAt (x : ℝ) :
    HasDerivAt p.fractionalTangent
      ((p.fractionalCurvature x:ℂ)*Complex.I*p.fractionalTangent x) x := by
  let u := p.arclengthInverse (p.length*x)
  have h1 := (p.inverse_hasDerivAt (p.length*x)).comp x ((hasDerivAt_id x).const_mul p.length)
  have h2 := (tangent_hasDerivAt p.smooth p.regular _).scomp x h1
  apply h2.congr_deriv
  change ((speed p.position u)⁻¹*(p.length*1)) •
    (((speed p.position u*curvature p.position u : ℝ):ℂ)*normal p.position u) =
    (((p.length*curvature p.position u:ℝ):ℂ)*Complex.I*tangent p.position u)
  rw [Complex.real_smul,normal]
  push_cast
  have ng : (speed p.position u:ℂ)≠0 := by exact_mod_cast (speed_pos p.regular u).ne'
  field_simp

theorem fractionalTangent_mean : (∫ x in 0..1,p.fractionalTangent x)=0 := by
  let f := fun s=>tangent p.position (p.arclengthInverse s)
  have cf : Continuous f := (tangent_smooth p.smooth p.regular).continuous.comp p.inverse_continuous
  have eq := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=p.length)
    (fun s _=>p.unit_position_hasDerivAt s) (cf.intervalIntegrable ..)
  have ep : p.unitSpeedPosition p.length=p.unitSpeedPosition 0 := by
    simp only [unitSpeedPosition,p.inverse_length,p.inverse_zero]
    simpa using p.periodic 0
  change (∫ s in 0..p.length,f s)=_ at eq
  rw [ep,sub_self] at eq
  change (∫ x in 0..1,f (p.length*x))=0
  rw [intervalIntegral.integral_comp_mul_left f p.length_pos.ne',mul_zero,mul_one,eq,smul_zero]

theorem fractionalCurvature_mean :
    (∫ x in 0..1,p.fractionalCurvature x) =
      ∫ u in 0..p.period,curvature p.position u*speed p.position u := by
  let f := fun s=>curvature p.position (p.arclengthInverse s)
  change (∫x in 0..1,p.length*f (p.length*x))=_
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_mul_left f p.length_pos.ne',
    mul_zero,mul_one,smul_eq_mul,←mul_assoc,mul_inv_cancel₀ p.length_pos.ne',one_mul]
  exact p.integral_comp_inverse (f:=curvature p.position) (curvature_smooth p.smooth p.regular).continuous

theorem fractionalCurvature_oscillation (S : ℝ) :
    (∫x in 0..1,(p.fractionalCurvature x-S)^2) =
      p.length * (∫ u in 0..p.period,
        (curvature p.position u-S/p.length)^2*speed p.position u) := by
  let f := fun s=>(curvature p.position (p.arclengthInverse s)-S/p.length)^2
  have eq : (fun x=>(p.fractionalCurvature x-S)^2)=fun x=>p.length^2*f (p.length*x) := by
    funext x
    dsimp only [fractionalCurvature,f]
    field_simp [p.length_pos.ne']
  rw [eq,intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_mul_left f p.length_pos.ne',
    mul_zero,mul_one,smul_eq_mul,←mul_assoc]
  have exactl : p.length^2*p.length⁻¹=p.length := by field_simp
  rw [exactl]
  congr 1
  exact p.integral_comp_inverse (f:=fun u=>(curvature p.position u-S/p.length)^2)
    (((curvature_smooth p.smooth p.regular).continuous.sub continuous_const).pow 2)

end MigrationGeometry.Flow.PeriodicRegularPosition
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

def materialSlice {t : ℝ} (ht : t ∈ I) : PeriodicRegularPosition :=
  ⟨c.period,c.period_pos,c.position t,c.position_slice_smooth ht,c.periodic t ht,c.immersion t ht⟩

/-- Parseval, closure and the oriented first moment for the unit tangent
obtained by reparametrizing the actual immersed material curve. -/
theorem material_tangent_fourier_data {t : ℝ} (ht : t ∈ I)
    (turn : c.signedCurvatureIntegral t=2*Real.pi) :
    let T := (c.materialSlice ht).fractionalTangent
    LowDefect.Tangent.coeff T 0=0 ∧ HasSum (LowDefect.Tangent.energy T) 1 ∧
    HasSum (fun n : ℤ=>(n:ℝ)*LowDefect.Tangent.energy T n) 1 ∧
    HasSum (fun n : ℤ=>((n:ℝ)-1)^2*LowDefect.Tangent.energy T n)
      (c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2) := by
  let p := c.materialSlice ht
  have ck : Continuous p.fractionalCurvature := continuous_const.mul
    ((curvature_smooth p.smooth p.regular).continuous.comp
      (p.inverse_continuous.comp (continuous_const.mul continuous_id)))
  have per : p.fractionalTangent 1=p.fractionalTangent 0 := by
    simp only [PeriodicRegularPosition.fractionalTangent,mul_one,mul_zero,p.inverse_length,p.inverse_zero]
    simpa using tangent_periodic p.smooth p.periodic 0
  have mean := p.fractionalCurvature_mean
  change _=c.signedCurvatureIntegral t at mean
  rw [turn] at mean
  have identity := LowDefect.Tangent.tangent_data ck (p.fractionalTangent_hasDerivAt)
    (fun _=>tangent_unit p.regular _) per mean p.fractionalTangent_mean
  rw [p.fractionalCurvature_oscillation] at identity
  exact identity

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.material_tangent_fourier_data
