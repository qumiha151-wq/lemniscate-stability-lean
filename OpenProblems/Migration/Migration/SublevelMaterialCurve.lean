import Migration.SublevelArclength
import Migration.LowDefectMaterialModes
import Migration.LowDefectPhysicalDisk

noncomputable section
open Set MeasureTheory
namespace MigrationGeometry.Flow.PeriodicRegularPosition
variable (p : PeriodicRegularPosition)

def bendingCurve : LowBending.ClosedFrenetCurve where
  period := p.length
  period_pos := p.length_pos
  curve := p.unitSpeedPosition
  tangent := fun s=>tangent p.position (p.arclengthInverse s)
  curvature := fun s=>curvature p.position (p.arclengthInverse s)
  curvature₁ := fun s=>curvatureGradient p.position (p.arclengthInverse s)
  curvature₂ := fun s=>curvatureSecond p.position (p.arclengthInverse s)
  curve_periodic := fun s=>by
    change p.position (p.arclengthInverse (s+p.length))=_
    rw [p.inverse_add_length,p.periodic]
    rfl
  tangent_periodic := fun s=>by dsimp only; rw [p.inverse_add_length,tangent_periodic p.smooth p.periodic]
  curvature_periodic := fun s=>by dsimp only; rw [p.inverse_add_length,curvature_periodic p.smooth p.regular p.periodic]
  curvature₁_periodic := fun s=>by dsimp only; rw [p.inverse_add_length,curvatureGradient_periodic p.smooth p.regular p.periodic]
  curve_deriv := p.unit_position_hasDerivAt
  tangent_deriv := fun s=>by
    apply ((tangent_hasDerivAt p.smooth p.regular (p.arclengthInverse s)).scomp s (p.inverse_hasDerivAt s)).congr_deriv
    rw [Complex.real_smul]
    push_cast
    field_simp [show (speed p.position (p.arclengthInverse s):ℂ)≠0 by exact_mod_cast (speed_pos p.regular _).ne']
    simp [normal,mul_assoc]
  curvature_deriv := fun s=>by
    apply ((curvature_hasDerivAt p.smooth p.regular (p.arclengthInverse s)).comp s (p.inverse_hasDerivAt s)).congr_deriv
    field_simp [(speed_pos p.regular _).ne']
  curvature₁_deriv := fun s=>by
    apply ((curvatureGradient_hasDerivAt p.smooth p.regular (p.arclengthInverse s)).comp s (p.inverse_hasDerivAt s)).congr_deriv
    field_simp [(speed_pos p.regular _).ne']
  curvature₂_continuous := (curvatureSecond_smooth p.smooth p.regular).continuous.comp p.inverse_continuous
  tangent_unit := fun _=>tangent_unit p.regular _

theorem bendingCurve_turn : (∫s in 0..p.bendingCurve.period,p.bendingCurve.curvature s)=
    ∫u in 0..p.period,curvature p.position u*speed p.position u :=
  p.integral_comp_inverse (curvature_smooth p.smooth p.regular).continuous

theorem bendingCurve_energy : p.bendingCurve.energy=
    (∫u in 0..p.period,(curvature p.position u)^2*speed p.position u)/2 := by
  unfold LowBending.ClosedFrenetCurve.energy
  rw [show (∫s in 0..p.bendingCurve.period,p.bendingCurve.curvature s^2)=
      ∫u in 0..p.period,(curvature p.position u)^2*speed p.position u from
    p.integral_comp_inverse ((curvature_smooth p.smooth p.regular).continuous.pow 2)]

theorem bendingCurve_dissipation : p.bendingCurve.dissipation=
    ∫u in 0..p.period,(force p.position u)^2*speed p.position u :=
  p.integral_comp_inverse ((force_smooth p.smooth p.regular).continuous.pow 2)

theorem bendingCurve_lengthRate : (∫s in 0..p.bendingCurve.period,p.bendingCurve.curvature s*p.bendingCurve.force s)=
    ∫u in 0..p.period,curvature p.position u*force p.position u*speed p.position u :=
  p.integral_comp_inverse ((curvature_smooth p.smooth p.regular).continuous.mul (force_smooth p.smooth p.regular).continuous)

end MigrationGeometry.Flow.PeriodicRegularPosition
#print axioms MigrationGeometry.Flow.PeriodicRegularPosition.bendingCurve_lengthRate
