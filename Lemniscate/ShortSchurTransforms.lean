import Lemniscate.ShortSchurInputs

/-! Enclosures of the actual Householder, neutral and projection matrices. -/
namespace Lemniscate.CoarseArithmetic
open Matrix Finset

def shortSubtract (I J : Interval) : Interval := add I (scale J (-1))

theorem short_subtract_sound (I J : Interval) (x y : ℝ)
    (hx : Contains I x) (hy : Contains J y) : Contains (shortSubtract I J) (x-y) := by
  simpa only [shortSubtract, Rat.cast_neg, Rat.cast_one, mul_neg_one, sub_eq_add_neg]
    using add_sound _ _ _ _ hx (scale_sound _ _ (-1) hy)

def shortDivide (I J : Interval) : Interval := roundInterval 18 (dividePositive I J)

theorem short_divide_sound (I J : Interval) (x y : ℝ) (hp : 0 < J.lo)
    (hx : Contains I x) (hy : Contains J y) : Contains (shortDivide I J) (x/y) :=
  roundInterval_sound _ _ _ (dividePositive_sound _ _ _ _ hp hx hy)

def shortDeltaInput (i j : Fin 15) : Interval := point (if i=j then 1 else 0)

theorem short_delta_input_sound (i j : Fin 15) :
    Contains (shortDeltaInput i j) ((1 : Matrix (Fin 15) (Fin 15) ℝ) i j) := by
  by_cases hij : i=j
  · simpa only [shortDeltaInput, if_pos hij, one_apply, hij, ite_true,
      Rat.cast_one] using point_sound 1
  · simpa only [shortDeltaInput, if_neg hij, one_apply, if_neg hij,
      Rat.cast_zero] using point_sound 0

def shortHouseholderDenInput : Interval := add (point 1)
  ⟨∑ i : Fin 15, (mul (shortRotationHeadInput i) (shortAnchorHeadInput i)).lo,
   ∑ i : Fin 15, (mul (shortRotationHeadInput i) (shortAnchorHeadInput i)).hi⟩

theorem short_householder_den_input_sound : Contains shortHouseholderDenInput
    (1 + ∑ i : Fin 15, shortRotationHead shortActualCoefficient i * shortAnchorHead i) := by
  have hs := sum_interval_sound _ _ (fun i : Fin 15 => mul_sound _ _ _ _
    (short_rotation_head_input_sound i) (short_anchor_head_input_sound i))
  simpa only [shortHouseholderDenInput, Rat.cast_one] using
    add_sound _ _ _ _ (point_sound 1) hs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem short_householder_den_input_pos : 0 < shortHouseholderDenInput.lo := by decide +kernel

def shortHouseholderInput (i j : Fin 15) : Interval :=
  shortSubtract (shortDeltaInput i j) (shortDivide
    (mul (add (shortRotationHeadInput i) (shortAnchorHeadInput i))
      (add (shortRotationHeadInput j) (shortAnchorHeadInput j))) shortHouseholderDenInput)

theorem short_householder_input_sound : MatrixContains shortHouseholderInput
    (shortHouseholder shortActualCoefficient) := by
  intro i j
  have hn := mul_sound _ _ _ _
    (add_sound _ _ _ _ (short_rotation_head_input_sound i) (short_anchor_head_input_sound i))
    (add_sound _ _ _ _ (short_rotation_head_input_sound j) (short_anchor_head_input_sound j))
  have hq := short_divide_sound _ _ _ _ short_householder_den_input_pos hn
    short_householder_den_input_sound
  have hh := short_subtract_sound _ _ _ _ (short_delta_input_sound i j) hq
  have heq : shortHouseholder shortActualCoefficient i j =
      (1 : Matrix (Fin 15) (Fin 15) ℝ) i j -
      (shortRotationHead shortActualCoefficient i + shortAnchorHead i) *
      (shortRotationHead shortActualCoefficient j + shortAnchorHead j) /
      (1 + ∑ r, shortRotationHead shortActualCoefficient r * shortAnchorHead r) := by
    simp only [shortHouseholder, shortOuter, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, Pi.add_apply]
    ring
  rw [heq]
  exact hh

def shortNeutralInput (i j : Fin 15) : Interval := add (shortDeltaInput i j)
  (roundInterval 18 (mul (shortRotationHeadInput i)
    (shortSubtract (shortAdjointHeadInput j) (shortRotationHeadInput j))))

def shortNeutralInvInput (i j : Fin 15) : Interval := shortSubtract (shortDeltaInput i j)
  (roundInterval 18 (mul (shortRotationHeadInput i)
    (shortSubtract (shortAdjointHeadInput j) (shortRotationHeadInput j))))

theorem short_neutral_input_sound : MatrixContains shortNeutralInput
    (shortNeutral shortActualCoefficient) := by
  intro i j
  have h := add_sound _ _ _ _ (short_delta_input_sound i j)
    (roundInterval_sound 18 _ _ (mul_sound _ _ _ _ (short_rotation_head_input_sound i)
      (short_subtract_sound _ _ _ _ (short_adjoint_head_input_sound j)
        (short_rotation_head_input_sound j))))
  simpa only [shortNeutralInput, shortNeutral, shortOuter, Matrix.add_apply, Pi.sub_apply] using h

theorem short_neutral_inv_input_sound : MatrixContains shortNeutralInvInput
    (shortNeutralInv shortActualCoefficient) := by
  intro i j
  have h := short_subtract_sound _ _ _ _ (short_delta_input_sound i j)
    (roundInterval_sound 18 _ _ (mul_sound _ _ _ _ (short_rotation_head_input_sound i)
      (short_subtract_sound _ _ _ _ (short_adjoint_head_input_sound j)
        (short_rotation_head_input_sound j))))
  simpa only [shortNeutralInvInput, shortNeutralInv, shortOuter, Matrix.sub_apply, Pi.sub_apply] using h

def shortCenterInput (i j : Fin 15) : Interval :=
  roundInterval 18 (mul (shortAnchorHeadInput i) (shortAnchorHeadInput j))

theorem short_center_input_sound : MatrixContains shortCenterInput shortCenterProjection :=
  fun i j => roundInterval_sound 18 _ _
    (mul_sound _ _ _ _ (short_anchor_head_input_sound i) (short_anchor_head_input_sound j))

def shortStableInput (i j : Fin 15) : Interval :=
  shortSubtract (shortDeltaInput i j) (shortCenterInput i j)

theorem short_stable_input_sound : MatrixContains shortStableInput shortStableProjection :=
  fun i j => short_subtract_sound _ _ _ _ (short_delta_input_sound i j)
    (short_center_input_sound i j)

end Lemniscate.CoarseArithmetic
