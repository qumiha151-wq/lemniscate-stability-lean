import Lemniscate.RealHeadMatrices
import Lemniscate.IntervalMatrices

/-! Initial real enclosures for the actual finite Fourier vectors and period
parameter. The positive Householder denominator is checked by the kernel. -/
namespace Lemniscate.CoarseArithmetic

def roundedPositiveDivide (digits : ℕ) (I J : Interval) : Interval :=
  roundInterval digits (mul I (roundInterval digits (reciprocalPositive J)))

theorem rounded_positive_divide_sound (digits : ℕ) (I J : Interval) (x y : ℝ)
    (hJ : 0 < J.lo) (hx : Contains I x) (hy : Contains J y) :
    Contains (roundedPositiveDivide digits I J) (x/y) := by
  have h := roundInterval_sound digits _ _ (mul_sound _ _ _ _ hx
    (roundInterval_sound digits _ _ (reciprocalPositive_sound J y hJ hy)))
  simpa only [roundedPositiveDivide, one_div, div_eq_mul_inv, one_mul] using h

def finiteSineInput (I : Fin 15 → Interval) (i : Fin 31) : Interval :=
  if hi : i.val < 15 then scale (roundedPositiveDivide 30 (I ⟨14-i.val, by omega⟩) sqrtTwoData) (-1)
  else if hi : 15 < i.val then roundedPositiveDivide 30 (I ⟨i.val-16, by omega⟩) sqrtTwoData
  else point 0

theorem finite_sine_input_sound (I : Fin 15 → Interval) (v : Fin 15 → ℝ)
    (hv : ∀ j, Contains (I j) (v j)) (i : Fin 31) :
    Contains (finiteSineInput I i) (finiteSineCoordinate v i) := by
  unfold finiteSineInput finiteSineCoordinate
  split_ifs with hi hj
  · let j : Fin 15 := ⟨14-i.val, by omega⟩
    have h := rounded_positive_divide_sound 30 (I j) sqrtTwoData (v j) (Real.sqrt 2)
      vector_interval_certificate.sqrt_two_pos (hv j) sqrt_two_data_sound
    simpa only [Rat.cast_neg, Rat.cast_one, mul_neg_one, neg_div] using scale_sound _ _ (-1) h
  · exact rounded_positive_divide_sound 30 _ _ _ _
      vector_interval_certificate.sqrt_two_pos (hv _) sqrt_two_data_sound
  · simpa only [Rat.cast_zero] using point_sound 0

def finiteRotationInput : Fin 31 → Interval := finiteSineInput rotationFiniteData
def finiteAdjointInput : Fin 31 → Interval := finiteSineInput adjointFiniteData
def finiteAnchorInput : Fin 31 → Interval :=
  finiteSineInput (fun j => point (if j = 0 then 1 else 0))

theorem finite_rotation_input_sound (i : Fin 31) :
    Contains (finiteRotationInput i) (finiteRotationHead i) :=
  finite_sine_input_sound rotationFiniteData rotationFiniteCoefficient rotation_finite_data_sound i

theorem finite_adjoint_input_sound (i : Fin 31) :
    Contains (finiteAdjointInput i) (finiteAdjointHead i) :=
  finite_sine_input_sound adjointFiniteData adjointFiniteCoefficient adjoint_finite_data_sound i

theorem finite_anchor_sine_coordinate (i : Fin 31) :
    finiteAnchorHead i = finiteSineCoordinate (fun j => if j = 0 then 1 else 0) i := by
  fin_cases i <;> norm_num [finiteAnchorHead, finiteSineCoordinate, evenHeadFrequency] <;> ring

theorem finite_anchor_input_sound (i : Fin 31) :
    Contains (finiteAnchorInput i) (finiteAnchorHead i) := by
  rw [finite_anchor_sine_coordinate]
  apply finite_sine_input_sound
  intro j
  by_cases hj : j = 0
  · simpa only [if_pos hj, Rat.cast_one] using point_sound 1
  · simpa only [if_neg hj, Rat.cast_zero] using point_sound 0

def finitePeriodInput : Interval := ⟨thetaRLower,thetaRUpper⟩

theorem finite_period_input_sound : Contains finitePeriodInput thetaParameter :=
  actual_nome_theta_r_bounds

def finiteDifferenceInput (i j : Fin 31) : Interval :=
  fineCoefficientData ((evenHeadFrequency i-evenHeadFrequency j).natAbs/2)

theorem finite_difference_input_sound (i j : Fin 31) :
    Contains (finiteDifferenceInput i j)
      (fourierCoefficient thetaParameter nome ((evenHeadFrequency i-evenHeadFrequency j).natAbs/2)) := by
  have hi := i.isLt
  have hj := j.isLt
  have hindex : (evenHeadFrequency i-evenHeadFrequency j).natAbs/2 < 59 := by
    dsimp only [evenHeadFrequency]
    omega
  exact fine_coefficient_data_sound ⟨_, hindex⟩

def finiteHouseholderDenInput : Interval :=
  add (point 1) ⟨∑ i : Fin 31, (roundInterval 30 (mul (finiteRotationInput i) (finiteAnchorInput i))).lo,
    ∑ i : Fin 31, (roundInterval 30 (mul (finiteRotationInput i) (finiteAnchorInput i))).hi⟩

theorem finite_householder_den_input_sound : Contains finiteHouseholderDenInput
    (1+∑ i : Fin 31, finiteRotationHead i*finiteAnchorHead i) := by
  unfold finiteHouseholderDenInput
  apply add_sound _ _ _ _ (by simpa only [Rat.cast_one] using point_sound 1)
  exact sum_interval_sound _ _ (fun i => roundInterval_sound 30 _ _
    (mul_sound _ _ _ _ (finite_rotation_input_sound i) (finite_anchor_input_sound i)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finite_householder_den_input_pos : 0 < finiteHouseholderDenInput.lo := by
  decide +kernel

end Lemniscate.CoarseArithmetic
