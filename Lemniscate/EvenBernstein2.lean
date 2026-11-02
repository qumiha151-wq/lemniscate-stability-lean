import Lemniscate.EvenStageCalculus
import Lemniscate.EvenFactorData
import Lemniscate.EvenStageC0
import Lemniscate.EvenStageC1
import Lemniscate.EvenStageC2

namespace Lemniscate.CoarseArithmetic
def evenBernstein2IntegerComputed : Matrix (Fin 31) (Fin 31) IntegerInterval := integerMatrixAdd (integerMatrixAdd (evenStageC0IntegerMatrix) (integerMatrixScale (integerPoint (1/4)) evenStageC1IntegerMatrix)) (integerMatrixScale (integerPoint (1/24)) evenStageC2IntegerMatrix)
def evenBernstein2Computed : Matrix (Fin 31) (Fin 31) Interval := integerMatrixInterval evenBernstein2IntegerComputed
noncomputable def evenBernstein2Real : Matrix (Fin 31) (Fin 31) ℝ := ((evenStageC0Real)+((1/4):ℝ) • evenStageC1Real)+((1/24):ℝ) • evenStageC2Real
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem even_bernstein_2_comparison : ∀ i j,
    Encloses (evenBernsteinInterval 2 i j) (evenBernstein2Computed i j) := by
  unfold Encloses
  decide +kernel
theorem even_bernstein_2_sound : MatrixContains (evenBernsteinInterval 2) evenBernstein2Real := by
  simpa only [evenBernstein2Real, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
    (matrix_contains_enlargement (evenBernsteinInterval 2) evenBernstein2Computed _
      even_bernstein_2_comparison (integer_matrix_add_sound _ _ _ _ (integer_matrix_add_sound _ _ _ _ even_stage_c0_sound (integer_matrix_rational_scale_sound (1/4) _ _ even_stage_c1_sound)) (integer_matrix_rational_scale_sound (1/24) _ _ even_stage_c2_sound)))
end Lemniscate.CoarseArithmetic
