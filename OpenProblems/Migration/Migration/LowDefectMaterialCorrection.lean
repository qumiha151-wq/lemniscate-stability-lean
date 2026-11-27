import Migration.LowDefectNormalCorrection
import Migration.LowDefectSecondHarmonic

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.PeriodicRegularPosition
variable (p : PeriodicRegularPosition)

/-- Position centered at B and rescaled to perimeter 2π, using actual
fractional arclength labels x of period 1. -/
def fractionalPosition (B : ℂ) (x : ℝ) : ℂ :=
  (2*Real.pi/p.length) • (p.unitSpeedPosition (p.length*x)-B)

theorem fractionalPosition_der (B : ℂ) (x : ℝ) :
    HasDerivAt (p.fractionalPosition B) ((2*Real.pi:ℂ)*p.fractionalTangent x) x := by
  have comp := (p.unit_position_hasDerivAt (p.length*x)).scomp x ((hasDerivAt_id x).const_mul p.length)
  have deriv := (comp.sub_const B).const_smul (2*Real.pi/p.length)
  apply deriv.congr_deriv
  change (2*Real.pi/p.length) • ((p.length*1) • p.fractionalTangent x) = _
  rw [smul_smul,mul_one,div_mul_cancel₀ _ p.length_pos.ne',Complex.real_smul]
  push_cast
  rfl

theorem fractionalPosition_per (B : ℂ) : p.fractionalPosition B 1=p.fractionalPosition B 0 := by
  simp only [fractionalPosition,unitSpeedPosition,mul_one,mul_zero,p.inverse_length,p.inverse_zero]
  rw [show p.position p.period=p.position 0 by simpa using p.periodic 0]

end MigrationGeometry.Flow.PeriodicRegularPosition
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem material_fractional_position_mean {t : ℝ} (ht : t ∈ I) :
    (∫x in (0:ℝ)..1,(c.materialSlice ht).fractionalPosition (c.arclengthCentroid t) x)=0 := by
  let p := c.materialSlice ht
  let B := c.arclengthCentroid t
  let f := fun s=>p.unitSpeedPosition s-B
  change (∫x in (0:ℝ)..1,(2*Real.pi/p.length) • f (p.length*x))=0
  rw [intervalIntegral.integral_smul,intervalIntegral.integral_comp_mul_left f p.length_pos.ne',mul_zero,mul_one]
  have cy : Continuous (fun u=>p.position u-B) := p.smooth.continuous.sub continuous_const
  have mean := p.integral_complex_comp_inverse (fun u=>p.position u-B) cy
  change (∫s in 0..p.length,f s)=_ at mean
  rw [mean]
  have csp := (speed_smooth p.smooth p.regular).continuous
  simp only [smul_sub]
  rw [intervalIntegral.integral_sub (f:=fun u=>speed p.position u • p.position u)
    (g:=fun u=>speed p.position u • B) ((csp.smul p.smooth.continuous).intervalIntegrable ..)
    ((csp.smul (continuous_const (y:=B))).intervalIntegrable ..),intervalIntegral.integral_smul_const]
  have eq : (∫u in 0..p.period,speed p.position u • p.position u) -
      (∫u in 0..p.period,speed p.position u) • B=0 := by
    change (∫u in 0..c.period,speed (c.position t) u • c.position t u) -
      c.coreLength t • ((c.coreLength t)⁻¹ • (∫u in 0..c.period,speed (c.position t) u • c.position t u))=0
    rw [smul_smul,mul_inv_cancel₀ (c.coreLength_pos ht).ne',one_smul,sub_self]
  rw [eq,smul_zero,smul_zero]

/-- Sharp normal correction from a true material curve. Both position and
tangent are reconstructed by the inverse of the actual cumulative length. -/
theorem material_normal_correction {t : ℝ} (ht : t ∈ I)
    (turn : c.signedCurvatureIntegral t=2*Real.pi)
    (small : c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2 ≤ 14/100) :
    let p := c.materialSlice ht
    let G := p.fractionalPosition (c.arclengthCentroid t)
    let T := p.fractionalTangent
    (∫x in (0:ℝ)..1,‖G x+Complex.I*T x‖^2) ≤ (75/100)^2 *
      (c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2) := by
  let p := c.materialSlice ht
  let T := p.fractionalTangent
  let B := c.arclengthCentroid t
  let G := p.fractionalPosition B
  let D := c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2
  have ct : Continuous T := continuous_iff_continuousAt.mpr
    fun x=>(p.fractionalTangent_hasDerivAt x).continuousAt
  have gz : LowDefect.Tangent.coeff G 0=0 := by
    have m := c.material_fractional_position_mean ht
    change (∫x in (0:ℝ)..1,G x)=0 at m
    simp [LowDefect.Tangent.coeff,fourierCoeffOn_eq_integral,m]
  obtain ⟨h0,hm,h1,h2⟩:=c.material_tangent_fourier_data ht turn
  have bnd := LowDefect.Tangent.normal_correction_moment ct (p.fractionalPosition_der B)
    (p.fractionalPosition_per B) gz h0 hm h1 h2
  have c2 := (c.material_second_harmonic_bounds ht turn small).2
  change ‖LowDefect.Tangent.coeff T 2‖ ≤ (266/1000)*D at c2
  have c2sq := pow_le_pow_left₀ (norm_nonneg _) c2 2
  have d0 : 0≤D := div_nonneg (c.curvatureOscillation_nonneg ht _) (sq_nonneg _)
  change D≤14/100 at small
  change _≤5/9*D+7/12*‖LowDefect.Tangent.coeff T 2‖^2 at bnd
  change _≤(75/100)^2*D
  nlinarith only [bnd,c2sq,mul_le_mul_of_nonneg_right small d0,d0]

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.material_normal_correction
