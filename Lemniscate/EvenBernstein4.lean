import Lemniscate.EvenStageCalculus
import Lemniscate.EvenFactorData
import Lemniscate.EvenStageC0
import Lemniscate.EvenStageC1
import Lemniscate.EvenStageC2
import Lemniscate.EvenStageC4
import Lemniscate.EvenStageV3P

namespace Lemniscate.CoarseArithmetic
def evenBernstein4IntegerComputed : Matrix (Fin 31) (Fin 31) IntegerInterval := integerMatrixAdd (integerMatrixAdd (integerMatrixAdd (integerMatrixAdd (evenStageC0IntegerMatrix) (integerMatrixScale (integerPoint (1/2)) evenStageC1IntegerMatrix)) (integerMatrixScale (integerPoint (1/4)) evenStageC2IntegerMatrix)) (integerMatrixScale (integerPoint (1/8)) evenStageV3PIntegerMatrix)) (integerMatrixScale (integerPoint (1/16)) evenStageC4IntegerMatrix)
def evenBernstein4Computed : Matrix (Fin 31) (Fin 31) Interval := integerMatrixInterval evenBernstein4IntegerComputed
noncomputable def evenBernstein4Real : Matrix (Fin 31) (Fin 31) ℝ := ((((evenStageC0Real)+((1/2):ℝ) • evenStageC1Real)+((1/4):ℝ) • evenStageC2Real)+((1/8):ℝ) • evenStageV3PReal)+((1/16):ℝ) • evenStageC4Real
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem even_bernstein_4_comparison : ∀ i j,
    Encloses (evenBernsteinInterval 4 i j) (evenBernstein4Computed i j) := by
  unfold Encloses
  decide +kernel
theorem even_bernstein_4_sound : MatrixContains (evenBernsteinInterval 4) evenBernstein4Real := by
  simpa only [evenBernstein4Real, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
    (matrix_contains_enlargement (evenBernsteinInterval 4) evenBernstein4Computed _
      even_bernstein_4_comparison (integer_matrix_add_sound _ _ _ _ (integer_matrix_add_sound _ _ _ _ (integer_matrix_add_sound _ _ _ _ (integer_matrix_add_sound _ _ _ _ even_stage_c0_sound (integer_matrix_rational_scale_sound (1/2) _ _ even_stage_c1_sound)) (integer_matrix_rational_scale_sound (1/4) _ _ even_stage_c2_sound)) (integer_matrix_rational_scale_sound (1/8) _ _ even_stage_v3p_sound)) (integer_matrix_rational_scale_sound (1/16) _ _ even_stage_c4_sound)))
end Lemniscate.CoarseArithmetic
