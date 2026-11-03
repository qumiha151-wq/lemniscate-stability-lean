import Lemniscate.FiniteCoefficientIntervals
import Lemniscate.IntegerIntervalMatrices
import Lemniscate.EvenMatrixSeedData

/-! Soundness rules for the stored stages of the finite Bloch calculation. -/
namespace Lemniscate.CoarseArithmetic
open Matrix

theorem matrix_contains_enlargement {ι κ : Type*} (I J : Matrix ι κ Interval)
    (A : Matrix ι κ ℝ) (h : ∀ i j, Encloses (I i j) (J i j))
    (hJ : MatrixContains J A) : MatrixContains I A := by
  intro i j
  exact (hJ i j).mono (h i j).1 (h i j).2

def integerMatrixSymmetricPart {ι : Type*} (I : Matrix ι ι IntegerInterval) :
    Matrix ι ι IntegerInterval :=
  integerMatrixScale (integerPoint (1/2))
    (integerMatrixAdd I (integerMatrixTranspose I))

theorem integer_matrix_symmetric_part_sound
    (I : Matrix (Fin 31) (Fin 31) IntegerInterval) (A : Matrix (Fin 31) (Fin 31) ℝ)
    (hI : MatrixContains (integerMatrixInterval I) A) :
    MatrixContains (integerMatrixInterval (integerMatrixSymmetricPart I)) (realHeadHermitianPart A) := by
  have hc : Contains (integerPoint (1/2)).toInterval (1/2:ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using integer_point_sound (1/2)
  exact integer_matrix_scale_sound _ _ _ _ hc
    (integer_matrix_add_sound _ _ _ _ hI (integer_matrix_transpose_sound _ _ hI))

theorem integer_matrix_rational_scale_sound (q : ℚ)
    (I : Matrix (Fin 31) (Fin 31) IntegerInterval) (A : Matrix (Fin 31) (Fin 31) ℝ)
    (hI : MatrixContains (integerMatrixInterval I) A) :
    MatrixContains (integerMatrixInterval (integerMatrixScale (integerPoint q) I)) ((q:ℝ) • A) :=
  integer_matrix_scale_sound _ _ _ _ (integer_point_sound q) hI

def evenTopScalarInput : Interval := scale coefficientSquaredPeriodInput (-4)

theorem even_top_scalar_input_sound : Contains evenTopScalarInput (-4*lemniscateFrequencySquared^2) := by
  simpa only [evenTopScalarInput, Rat.cast_neg, Rat.cast_ofNat, mul_comm] using
    scale_sound _ _ (-4) coefficient_squared_period_input_sound

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem even_top_integer_comparison :
    IntegerEncloses evenTopIntegerData (integerInput evenTopScalarInput) := by
  unfold IntegerEncloses
  decide +kernel

theorem even_top_integer_input_sound : Contains evenTopIntegerData.toInterval (-4*lemniscateFrequencySquared^2) :=
  (integer_input_sound _ _ even_top_scalar_input_sound).mono
    (integer_encloses_sound _ _ even_top_integer_comparison).1
    (integer_encloses_sound _ _ even_top_integer_comparison).2

end Lemniscate.CoarseArithmetic
