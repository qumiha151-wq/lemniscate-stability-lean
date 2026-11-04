import Lemniscate.PeriodicParabolicSpace
/-! The parabolic space inherits the original ambient scalar norm.
This explicit instance keeps type-class matching on the closed submodule
from unfolding its integral constraints. -/
noncomputable section
namespace Lemniscate
variable (T : ℝ) [Fact (0 < T)] (τ : ℝ)
instance circleParabolicSpace_normedSpace :
    NormedSpace ℂ (CircleParabolicSpace T τ) where
  norm_smul_le c U := by
    change ‖c • (U : CircleParabolicAmbient T)‖ ≤ ‖c‖ * ‖(U : CircleParabolicAmbient T)‖
    exact norm_smul_le c (U : CircleParabolicAmbient T)
end Lemniscate
