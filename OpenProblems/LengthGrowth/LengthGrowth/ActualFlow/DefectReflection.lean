import LengthGrowth.ActualFlow.DefectOneTurn

noncomputable section
open MeasureTheory
namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

/-- Reflection reverses signed curvature and leaves the free elastic product
rate and both norms unchanged. -/
def bendingReflection : ClosedFrenetCurve where
  period := c.period
  period_pos := c.period_pos
  curve := fun s => star (c.curve s)
  tangent := fun s => star (c.tangent s)
  curvature := fun s => -c.curvature s
  curvature₁ := fun s => -c.curvature₁ s
  curvature₂ := fun s => -c.curvature₂ s
  curve_periodic := fun s => congrArg star (c.curve_periodic s)
  tangent_periodic := fun s => congrArg star (c.tangent_periodic s)
  curvature_periodic := fun s => congrArg Neg.neg (c.curvature_periodic s)
  curvature₁_periodic := fun s => congrArg Neg.neg (c.curvature₁_periodic s)
  curve_deriv := fun s => (c.curve_deriv s).star
  tangent_deriv := by
    intro s
    apply (c.tangent_deriv s).star.congr_deriv
    simp [star_mul]
    ring
  curvature_deriv := fun s => (c.curvature_deriv s).neg
  curvature₁_deriv := fun s => (c.curvature₁_deriv s).neg
  curvature₂_continuous := c.curvature₂_continuous.neg
  tangent_unit := fun s => by simp [c.tangent_unit]

theorem bending_reflection_energy : c.bendingReflection.energy=c.energy := by
  simp [energy,bendingReflection]

theorem bending_reflection_force (s : ℝ) : c.bendingReflection.force s= -c.force s := by
  dsimp [force,bendingReflection]
  ring

theorem bending_reflection_dissipation : c.bendingReflection.dissipation=c.dissipation := by
  change (∫ s in 0..c.period,c.bendingReflection.force s^2)=∫ s in 0..c.period,c.force s^2
  simp only [c.bending_reflection_force,neg_sq]

theorem bending_negative_turn_strict
    (turning : (∫ s in 0..c.period,c.curvature s)= -(2*Real.pi))
    (above : 4*Real.pi^2<2*c.energy*c.period)
    (below : 2*c.energy*c.period≤4*Real.pi^2+36) :
    c.energy*(∫ s in 0..c.period,c.curvature s*c.force s)<c.period*c.dissipation := by
  have t : (∫ s in 0..c.bendingReflection.period,c.bendingReflection.curvature s)=2*Real.pi := by
    change (∫ s in 0..c.period,-c.curvature s)=_
    rw [intervalIntegral.integral_neg,turning,neg_neg]
  have h := c.bendingReflection.bending_one_turn_strict t
    (by rwa [c.bending_reflection_energy]) (by rwa [c.bending_reflection_energy])
  rw [c.bending_reflection_energy,c.bending_reflection_dissipation] at h
  simp only [c.bending_reflection_force] at h
  change c.energy*(∫ s in 0..c.period,(-c.curvature s)*(-c.force s))<c.period*c.dissipation at h
  simpa only [neg_mul_neg] using h

end LengthGrowth.ClosedFrenetCurve
#print axioms LengthGrowth.ClosedFrenetCurve.bending_negative_turn_strict
