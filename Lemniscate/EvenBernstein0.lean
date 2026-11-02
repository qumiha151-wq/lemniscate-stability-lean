import Lemniscate.EvenStageCalculus
import Lemniscate.EvenFactorData
import Lemniscate.EvenStageC0

namespace Lemniscate.CoarseArithmetic
def evenBernstein0IntegerComputed : Matrix (Fin 31) (Fin 31) IntegerInterval := evenStageC0IntegerMatrix
def evenBernstein0Computed : Matrix (Fin 31) (Fin 31) Interval := integerMatrixInterval evenBernstein0IntegerComputed
noncomputable def evenBernstein0Real : Matrix (Fin 31) (Fin 31) ℝ := evenStageC0Real
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem even_bernstein_0_comparison : ∀ i j,
    Encloses (evenBernsteinInterval 0 i j) (evenBernstein0Computed i j) := by
  unfold Encloses
  decide +kernel
theorem even_bernstein_0_sound : MatrixContains (evenBernsteinInterval 0) evenBernstein0Real := by
  simpa only [evenBernstein0Real, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
    (matrix_contains_enlargement (evenBernsteinInterval 0) evenBernstein0Computed _
      even_bernstein_0_comparison even_stage_c0_sound)
end Lemniscate.CoarseArithmetic
