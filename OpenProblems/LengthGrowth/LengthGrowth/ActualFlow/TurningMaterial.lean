import LengthGrowth.ActualFlow.StrongArcScalar
import LengthGrowth.ActualFlow.TurningExcursions

noncomputable section
namespace LengthGrowth.ActualFlow.PeriodicRegularPosition

/-- At low normalized dissipation the actual curve necessarily contains
many disjoint subarcs with at least a quarter radian of net turning. -/
theorem has_turning_excursions_of_low_dissipation (p : PeriodicRegularPosition)
    (low : 4*(materialDissipation p.position p.period*p.length^2 /
      (8*(materialEnergy p.position p.period)^3))≤1) :
    ∃m : ℕ, p.HasTurningExcursions m ∧
      4*(materialEnergy p.position p.period*p.length)^2 ≤ (2^23:ℝ)*(m:ℝ)^6*
        (materialDissipation p.position p.period*p.length^2/(8*(materialEnergy p.position p.period)^3)) :=
  p.turning_excursions_transfer
    (fun hP hk per rms force cap turn =>
      MacroscopicTurning.scalar_excursions_of_low_force hP hk per rms force cap turn) low

end LengthGrowth.ActualFlow.PeriodicRegularPosition
#print axioms LengthGrowth.ActualFlow.PeriodicRegularPosition.has_turning_excursions_of_low_dissipation
