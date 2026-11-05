import Lemniscate.ShortSchurTransforms

/-! Enclosure of the genuine low-coordinate normalization and single shear. -/
namespace Lemniscate.CoarseArithmetic
open Matrix

def shortCosineBasisInput (n m : ℤ) : Interval :=
  if n=m ∨ n= -m then shortDivide (point 1) shortSqrtTwoInput else point 0

def shortSineBasisInput (n m : ℤ) : Interval :=
  if n=m then shortDivide (point 1) shortSqrtTwoInput
  else if n= -m then shortDivide (point (-1)) shortSqrtTwoInput else point 0

private theorem short_cosine_basis_input_sound (n m : ℤ) :
    Contains (shortCosineBasisInput n m)
      (if n=m ∨ n= -m then (1:ℝ)/Real.sqrt 2 else 0) := by
  unfold shortCosineBasisInput
  split_ifs
  · simpa only [Rat.cast_one] using short_divide_sound _ _ _ _
      (by norm_num [shortSqrtTwoInput]) (point_sound 1) short_sqrt_two_input_sound
  · simpa only [Rat.cast_zero] using point_sound 0

private theorem short_sine_basis_input_sound (n m : ℤ) :
    Contains (shortSineBasisInput n m)
      (if n=m then (1:ℝ)/Real.sqrt 2 else if n= -m then -1/Real.sqrt 2 else 0) := by
  unfold shortSineBasisInput
  split_ifs
  · simpa only [Rat.cast_one] using short_divide_sound _ _ _ _
      (by norm_num [shortSqrtTwoInput]) (point_sound 1) short_sqrt_two_input_sound
  · simpa only [Rat.cast_neg, Rat.cast_one] using short_divide_sound _ _ _ _
      (by norm_num [shortSqrtTwoInput]) (point_sound (-1)) short_sqrt_two_input_sound
  · simpa only [Rat.cast_zero] using point_sound 0

def shortLowBasisInput (i : Fin 15) (k : Fin 7) : Interval :=
  let n := shortHeadFrequency i
  ![point (if n=0 then 1 else 0),
    shortCosineBasisInput n 2, shortSineBasisInput n 2,
    shortCosineBasisInput n 4, shortSineBasisInput n 4,
    shortCosineBasisInput n 6, shortSineBasisInput n 6] k

theorem short_low_basis_input_sound (i : Fin 15) (k : Fin 7) :
    Contains (shortLowBasisInput i k) (shortLowBasis i k) := by
  fin_cases k
  · by_cases hi : shortHeadFrequency i=0
    · simpa [shortLowBasisInput, shortLowBasis, hi] using point_sound 1
    · simpa [shortLowBasisInput, shortLowBasis, hi] using point_sound 0
  all_goals first
    | exact short_cosine_basis_input_sound _ _
    | exact short_sine_basis_input_sound _ _

def shortLowWeightedBasisInput (i : Fin 15) (k : Fin 7) : Interval :=
  scale (shortLowBasisInput i k) (1/max 1 ((shortHeadFrequency i : ℚ)^2))

theorem short_low_weighted_basis_input_sound : MatrixContains shortLowWeightedBasisInput
    shortLowWeightedBasis := by
  intro i k
  have hw : ((1/max 1 ((shortHeadFrequency i : ℚ)^2) : ℚ) : ℝ) =
      1/max 1 ((shortHeadFrequency i : ℝ)^2) := by push_cast <;> rfl
  have h := scale_sound _ _ (1/max 1 ((shortHeadFrequency i : ℚ)^2))
    (short_low_basis_input_sound i k)
  rw [hw] at h
  simpa only [shortLowWeightedBasisInput, shortLowWeightedBasis, div_eq_mul_inv, one_mul] using h

def shortLowShearInput (i j : Fin 7) : Interval :=
  point ((if i=j then 1 else 0) + if i=0 ∧ j=2 then -(1/7:ℚ) else 0)

theorem short_low_shear_input_sound : MatrixContains shortLowShearInput shortLowShear := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shortLowShearInput, shortLowShear, shortLowShearPerturbation,
      Matrix.add_apply, Matrix.one_apply, Contains, point, Fin.ext_iff]

def shortLowRotationInput (i j : Fin 7) : Interval :=
  if i=1 ∧ j=1 ∨ i=1 ∧ j=3 ∨ i=3 ∧ j=1 then shortDivide (point 1) shortSqrtTwoInput
  else if i=3 ∧ j=3 then shortDivide (point (-1)) shortSqrtTwoInput
  else if i=j ∧ i≠1 ∧ i≠3 then point 1 else point 0

theorem short_low_rotation_input_sound : MatrixContains shortLowRotationInput shortLowRotation := by
  intro i j
  unfold shortLowRotationInput shortLowRotation
  split_ifs
  · simpa only [Rat.cast_one] using short_divide_sound _ _ _ _
      (by norm_num [shortSqrtTwoInput]) (point_sound 1) short_sqrt_two_input_sound
  · simpa only [Rat.cast_neg, Rat.cast_one] using short_divide_sound _ _ _ _
      (by norm_num [shortSqrtTwoInput]) (point_sound (-1)) short_sqrt_two_input_sound
  · simpa only [Rat.cast_one] using point_sound 1
  · simpa only [Rat.cast_zero] using point_sound 0

def shortLowEmbeddingInput : Matrix (Fin 15) (Fin 7) Interval :=
  intervalMatrixMul 18 shortLowWeightedBasisInput
    (intervalMatrixMul 18 shortLowShearInput shortLowRotationInput)

theorem short_low_embedding_input_sound : MatrixContains shortLowEmbeddingInput shortLowEmbedding :=
  interval_matrix_mul_sound 18 _ _ _ _ short_low_weighted_basis_input_sound
    (interval_matrix_mul_sound 18 _ _ _ _ short_low_shear_input_sound short_low_rotation_input_sound)

end Lemniscate.CoarseArithmetic
