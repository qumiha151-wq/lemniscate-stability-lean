import Migration.LowDefectMaterialCorrection

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.PeriodicRegularPosition
variable (p : PeriodicRegularPosition)

/-- Centered position in units of the radius of the m-fold circle. -/
def coverPosition (m : ℝ) (B : ℂ) (s : ℝ) : ℂ := m • p.fractionalPosition B s

def coverCorrection (m : ℝ) (B : ℂ) (s : ℝ) : ℂ :=
  p.coverPosition m B s+Complex.I*p.fractionalTangent s

def coverRate (m s : ℝ) : ℂ :=
  (2*Real.pi*m-p.fractionalCurvature s) • p.fractionalTangent s

theorem coverCorrection_derivative (m : ℝ) (B : ℂ) (s : ℝ) :
    HasDerivAt (p.coverCorrection m B) (p.coverRate m s) s := by
  apply (((p.fractionalPosition_der B s).const_smul m).add
    ((p.fractionalTangent_hasDerivAt s).const_mul Complex.I)).congr_deriv
  simp only [coverRate,Complex.real_smul,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_ofNat]
  linear_combination (p.fractionalCurvature s:ℂ)*p.fractionalTangent s*Complex.I_sq

theorem coverRate_continuous (m : ℝ) : Continuous (p.coverRate m) := by
  have ck : Continuous p.fractionalCurvature := continuous_const.mul
    ((curvature_smooth p.smooth p.regular).continuous.comp
      (p.inverse_continuous.comp (continuous_const.mul continuous_id)))
  exact (continuous_const.sub ck).smul (continuous_iff_continuousAt.mpr
    fun s=>(p.fractionalTangent_hasDerivAt s).continuousAt)

theorem coverCorrection_periodic (m : ℝ) (B : ℂ) : Function.Periodic (p.coverCorrection m B) 1 := by
  intro s
  simp only [coverCorrection,coverPosition,fractionalPosition,fractionalTangent,unitSpeedPosition,
    mul_add,mul_one,p.inverse_add_length,p.periodic _,tangent_periodic p.smooth p.periodic _]

theorem coverRate_norm_sq (m s : ℝ) :
    ‖p.coverRate m s‖^2=(p.fractionalCurvature s-2*Real.pi*m)^2 := by
  rw [coverRate,norm_smul,show ‖p.fractionalTangent s‖=1 from tangent_unit p.regular _,mul_one,Real.norm_eq_abs,sq_abs]
  ring

end MigrationGeometry.Flow.PeriodicRegularPosition
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem multi_correction_mean {t : ℝ} (ht : t∈I) (m : ℝ) :
    (∫s in (0:ℝ)..1,(c.materialSlice ht).coverCorrection m (c.arclengthCentroid t) s)=0 := by
  let p := c.materialSlice ht
  let B := c.arclengthCentroid t
  have cg : Continuous (p.fractionalPosition B) := continuous_iff_continuousAt.mpr
    fun s=>(p.fractionalPosition_der B s).continuousAt
  have ct : Continuous p.fractionalTangent := continuous_iff_continuousAt.mpr
    fun s=>(p.fractionalTangent_hasDerivAt s).continuousAt
  change (∫s in (0:ℝ)..1,m • p.fractionalPosition B s+Complex.I*p.fractionalTangent s)=0
  rw [intervalIntegral.integral_add (f:=fun s=>m • p.fractionalPosition B s)
    (g:=fun s=>Complex.I*p.fractionalTangent s) ((cg.const_smul m).intervalIntegrable ..)
    ((ct.const_mul Complex.I).intervalIntegrable ..),intervalIntegral.integral_smul,
    intervalIntegral.integral_const_mul,p.fractionalTangent_mean]
  have hz : (∫s in (0:ℝ)..1,p.fractionalPosition B s)=0 := c.material_fractional_position_mean ht
  rw [hz,smul_zero,mul_zero,add_zero]

theorem multi_rate_moment {t : ℝ} (ht : t∈I) (m : ℝ) :
    (∫s in (0:ℝ)..1,‖(c.materialSlice ht).coverRate m s‖^2)=
      c.curvatureOscillation (2*Real.pi*m) t := by
  simp_rw [PeriodicRegularPosition.coverRate_norm_sq]
  exact (c.materialSlice ht).fractionalCurvature_oscillation (2*Real.pi*m)

theorem multi_correction_moment {t : ℝ} (ht : t∈I) (m : ℝ) :
    (2*Real.pi)^2*(∫s in (0:ℝ)..1,‖(c.materialSlice ht).coverCorrection m (c.arclengthCentroid t) s‖^2)
      ≤c.curvatureOscillation (2*Real.pi*m) t := by
  let p := c.materialSlice ht
  let B := c.arclengthCentroid t
  have periodic := p.coverCorrection_periodic m B 0
  rw [zero_add] at periodic
  have w := LowDefect.periodic_wirtinger (by norm_num : (0:ℝ)<1) _ _ periodic
    (p.coverCorrection_derivative m B) (p.coverRate_continuous m) (c.multi_correction_mean ht m)
  simpa only [one_pow,one_mul,c.multi_rate_moment ht m,p,B] using w

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.multi_correction_moment
