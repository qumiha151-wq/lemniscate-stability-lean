import Lemniscate.PeriodicParabolicSpace

/-! The principal equation on the actual closed parabolic space. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ENNReal

variable (T : ℝ) [Fact (0 < T)]

/-- The actual time-L2 principal equation `v + u + 4 D^4 u`. -/
def circleParabolicPrincipalRHS (τ : ℝ) :
    CircleParabolicSpace T τ →L[ℂ] CircleTimeL2 T :=
  circleParabolicTimeDerivative T τ+
    (((circleSobolevCoordinate T 4 0+(4:ℂ) • circleSobolevCoordinate T 4 4).compLpL
      2 (volume : Measure unitInterval)).comp (circleParabolicH4 T τ))

end Lemniscate
