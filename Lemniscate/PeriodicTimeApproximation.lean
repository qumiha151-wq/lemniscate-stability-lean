import Lemniscate.PeriodicParabolicSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! Continuous time forcing is dense in the actual unit-interval L2 space.
This specializes Mathlib's continuous-function density theorem to the spatial
periodic L2 Hilbert space and the standard unit-interval volume measure.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ENNReal

variable (T : ℝ) [Fact (0 < T)]

local instance circleTimeApproximationSecondCountable :
    SecondCountableTopologyEither unitInterval (CircleL2 T) where
  out := Or.inl (inferInstance : SecondCountableTopology unitInterval)

theorem circle_time_continuous_dense_range :
    DenseRange (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℂ :
      C(unitInterval, CircleL2 T) →L[ℂ] CircleTimeL2 T) := by
  letI : (volume : Measure unitInterval).WeaklyRegular :=
    Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure
      (volume : Measure unitInterval)
  exact ContinuousMap.toLp_denseRange (E := CircleL2 T) (p := 2)
    (μ := (volume : Measure unitInterval)) (𝕜 := ℂ) (by norm_num)

end Lemniscate
