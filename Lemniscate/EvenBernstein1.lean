import Lemniscate.EvenStageCalculus
import Lemniscate.EvenFactorData
import Lemniscate.EvenStageC0
import Lemniscate.EvenStageC1

namespace Lemniscate.CoarseArithmetic
def evenBernstein1IntegerComputed : Matrix (Fin 31) (Fin 31) IntegerInterval := integerMatrixAdd (evenStageC0IntegerMatrix) (integerMatrixScale (integerPoint (1/8)) evenStageC1IntegerMatrix)
def evenBernstein1Computed : Matrix (Fin 31) (Fin 31) Interval := integerMatrixInterval evenBernstein1IntegerComputed
noncomputable def evenBernstein1Real : Matrix (Fin 31) (Fin 31) ℝ := (evenStageC0Real)+((1/8):ℝ) • evenStageC1Real
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem even_bernstein_1_comparison : ∀ i j,
    Encloses (evenBernsteinInterval 1 i j) (evenBernstein1Computed i j) := by
  unfold Encloses
  decide +kernel
theorem even_bernstein_1_sound : MatrixContains (evenBernsteinInterval 1) evenBernstein1Real := by
  simpa only [evenBernstein1Real, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
    (matrix_contains_enlargement (evenBernsteinInterval 1) evenBernstein1Computed _
      even_bernstein_1_comparison (integer_matrix_add_sound _ _ _ _ even_stage_c0_sound (integer_matrix_rational_scale_sound (1/8) _ _ even_stage_c1_sound)))
end Lemniscate.CoarseArithmetic
