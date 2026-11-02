import Lemniscate.EvenStageCalculus
import Lemniscate.EvenFactorData
import Lemniscate.EvenStageC0
import Lemniscate.EvenStageC1
import Lemniscate.EvenStageC2
import Lemniscate.EvenStageV3P

namespace Lemniscate.CoarseArithmetic
def evenBernstein3IntegerComputed : Matrix (Fin 31) (Fin 31) IntegerInterval := integerMatrixAdd (integerMatrixAdd (integerMatrixAdd (evenStageC0IntegerMatrix) (integerMatrixScale (integerPoint (3/8)) evenStageC1IntegerMatrix)) (integerMatrixScale (integerPoint (1/8)) evenStageC2IntegerMatrix)) (integerMatrixScale (integerPoint (1/32)) evenStageV3PIntegerMatrix)
def evenBernstein3Computed : Matrix (Fin 31) (Fin 31) Interval := integerMatrixInterval evenBernstein3IntegerComputed
noncomputable def evenBernstein3Real : Matrix (Fin 31) (Fin 31) ℝ := (((evenStageC0Real)+((3/8):ℝ) • evenStageC1Real)+((1/8):ℝ) • evenStageC2Real)+((1/32):ℝ) • evenStageV3PReal
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem even_bernstein_3_comparison : ∀ i j,
    Encloses (evenBernsteinInterval 3 i j) (evenBernstein3Computed i j) := by
  unfold Encloses
  decide +kernel
theorem even_bernstein_3_sound : MatrixContains (evenBernsteinInterval 3) evenBernstein3Real := by
  simpa only [evenBernstein3Real, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
    (matrix_contains_enlargement (evenBernsteinInterval 3) evenBernstein3Computed _
      even_bernstein_3_comparison (integer_matrix_add_sound _ _ _ _ (integer_matrix_add_sound _ _ _ _ (integer_matrix_add_sound _ _ _ _ even_stage_c0_sound (integer_matrix_rational_scale_sound (3/8) _ _ even_stage_c1_sound)) (integer_matrix_rational_scale_sound (1/8) _ _ even_stage_c2_sound)) (integer_matrix_rational_scale_sound (1/32) _ _ even_stage_v3p_sound)))
end Lemniscate.CoarseArithmetic
