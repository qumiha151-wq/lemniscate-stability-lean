import Lemniscate.ShortSchurTransforms

/-! Scalar Fourier formulas and enclosures of the true transformed matrices.
The five coefficients are derived from the differential expression, rather
than supplied as certificate assumptions. -/
namespace Lemniscate
open Matrix Finset

def shortAMonomial (k : Fin 5) (n m : ℤ) : ℚ :=
  ![(15/2:ℚ)*n*(7*m-n), (75/2:ℚ)*n+(105/2:ℚ)*m, 45, 0, 0] k

def shortADiagonal (k : Fin 5) (n : ℤ) : ℚ :=
  ![-4*(n:ℚ)^4, -16*(n:ℚ)^3, -24*(n:ℚ)^2, -16*(n:ℚ), -4] k

def shortAConstant (k : Fin 5) : ℚ := ![-42,0,0,0,0] k

theorem short_bloch_entry_eq (r : ℝ) (h : ℕ → ℝ) (k : Fin 5) (n m : ℤ) :
    shortBlochEntry r h k n m = (shortAMonomial k n m : ℝ)*r*h ((n-m).natAbs/2) +
      if n=m then (shortADiagonal k n : ℝ)*r^2+(shortAConstant k : ℝ) else 0 := by
  fin_cases k <;> by_cases hnm : n=m
  all_goals
    simp only [shortBlochEntry, shortAMonomial, shortADiagonal, shortAConstant,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons, Matrix.tail_cons, hnm, ite_true, ite_false]
    try subst m
    push_cast
    ring

end Lemniscate

namespace Lemniscate.CoarseArithmetic
open Matrix Finset

def shortFrequencySquareInput : Interval :=
  roundInterval 18 (mul shortFrequencyInterval shortFrequencyInterval)

theorem short_frequency_square_input_sound : Contains shortFrequencySquareInput
    (lemniscateFrequencySquared^2) := by
  apply roundInterval_sound
  simpa only [pow_two] using mul_sound _ _ _ _ short_frequency_enclosure
    short_frequency_enclosure

def shortBlochEntryInput (k : Fin 5) (n m : ℤ) : Interval :=
  add (scale (mul shortFrequencyInterval (shortCoefficientInput ((n-m).natAbs/2)))
    (shortAMonomial k n m))
    (if n=m then add (scale shortFrequencySquareInput (shortADiagonal k n))
      (point (shortAConstant k)) else point 0)

theorem short_bloch_entry_input_sound (k : Fin 5) (n m : ℤ) :
    Contains (shortBlochEntryInput k n m)
      (shortBlochEntry lemniscateFrequencySquared shortActualCoefficient k n m) := by
  rw [short_bloch_entry_eq]
  apply add_sound
  · simpa only [mul_assoc, mul_comm, mul_left_comm] using scale_sound _ _
      (shortAMonomial k n m) (mul_sound _ _ _ _ short_frequency_enclosure
        (short_coefficient_input_sound ((n-m).natAbs/2)))
  · by_cases hnm : n=m
    · simp only [if_pos hnm]
      simpa only [mul_comm] using add_sound _ _ _ _
        (scale_sound _ _ (shortADiagonal k n) short_frequency_square_input_sound)
        (point_sound (shortAConstant k))
    · simpa only [if_neg hnm, Rat.cast_zero] using point_sound 0

def shortBlochHeadInput (k : Fin 5) (i j : Fin 15) : Interval :=
  shortBlochEntryInput k (shortHeadFrequency i) (shortHeadFrequency j)

theorem short_bloch_head_input_sound (k : Fin 5) :
    MatrixContains (shortBlochHeadInput k)
      (shortBlochHead lemniscateFrequencySquared shortActualCoefficient k) :=
  fun i j => short_bloch_entry_input_sound k _ _

def shortSymmetricInput (M : Matrix (Fin 15) (Fin 15) Interval) :
    Matrix (Fin 15) (Fin 15) Interval :=
  intervalMatrixScale 18 (point (1/2)) (intervalMatrixAdd M (intervalMatrixTranspose M))

theorem short_symmetric_input_sound (I : Matrix (Fin 15) (Fin 15) Interval)
    (M : Matrix (Fin 15) (Fin 15) ℝ) (h : MatrixContains I M) :
    MatrixContains (shortSymmetricInput I) (shortSymmetric M) := by
  exact interval_matrix_scale_sound 18 _ _ _ _
    (by simpa using point_sound (1/2))
    (interval_matrix_add_sound _ _ _ _ h (interval_matrix_transpose_sound _ _ h))

def shortTransformedInput (k : Fin 5) : Matrix (Fin 15) (Fin 15) Interval :=
  if k=0 then intervalMatrixMul 18
    (intervalMatrixMul 18 shortHouseholderInput (shortSymmetricInput (shortBlochHeadInput 0)))
    shortHouseholderInput
  else if k=4 then intervalMatrixScale 18 (scale shortFrequencySquareInput (-4)) shortDeltaInput
  else shortSymmetricInput (intervalMatrixMul 18
    (intervalMatrixMul 18
      (intervalMatrixMul 18
        (intervalMatrixMul 18 shortHouseholderInput shortNeutralInput) (shortBlochHeadInput k))
      shortNeutralInvInput) shortHouseholderInput)

theorem short_transformed_input_sound (k : Fin 5) :
    MatrixContains (shortTransformedInput k)
      (shortTransformedCoefficient lemniscateFrequencySquared shortActualCoefficient k) := by
  by_cases hk : k=0
  · subst k
    exact interval_matrix_mul_sound 18 _ _ _ _
      (interval_matrix_mul_sound 18 _ _ _ _ short_householder_input_sound
        (short_symmetric_input_sound _ _ (short_bloch_head_input_sound 0)))
      short_householder_input_sound
  · by_cases hk4 : k=4
    · simp only [shortTransformedInput, shortTransformedCoefficient, if_neg hk, if_pos hk4]
      exact interval_matrix_scale_sound 18 _ _ _ _
        (by simpa only [Rat.cast_neg, Rat.cast_ofNat, mul_comm] using
          scale_sound _ _ (-4) short_frequency_square_input_sound)
        short_delta_input_sound
    · simp only [shortTransformedInput, shortTransformedCoefficient, if_neg hk, if_neg hk4]
      exact short_symmetric_input_sound _ _ (interval_matrix_mul_sound 18 _ _ _ _
        (interval_matrix_mul_sound 18 _ _ _ _
          (interval_matrix_mul_sound 18 _ _ _ _
            (interval_matrix_mul_sound 18 _ _ _ _ short_householder_input_sound
              short_neutral_input_sound) (short_bloch_head_input_sound k))
          short_neutral_inv_input_sound) short_householder_input_sound)

end Lemniscate.CoarseArithmetic
