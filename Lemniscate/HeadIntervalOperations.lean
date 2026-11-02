import Lemniscate.FiniteHeadInputIntervals

/-! Entrywise enclosures of the real finite transformations. These operations
can use stored intermediate intervals, avoiding repeated matrix evaluation. -/
namespace Lemniscate.CoarseArithmetic
open Matrix

def intervalSubtract (I J : Interval) : Interval := add I (scale J (-1))

theorem interval_subtract_sound (I J : Interval) (x y : ℝ)
    (hx : Contains I x) (hy : Contains J y) : Contains (intervalSubtract I J) (x-y) := by
  simpa only [intervalSubtract, Rat.cast_neg, Rat.cast_one, mul_neg_one, sub_eq_add_neg] using
    add_sound _ _ _ _ hx (scale_sound _ _ (-1) hy)

def headDeltaInput (i j : Fin 31) : Interval := point (if i = j then 1 else 0)

theorem head_delta_input_sound (i j : Fin 31) :
    Contains (headDeltaInput i j) (if i = j then (1:ℝ) else 0) := by
  by_cases hij : i = j
  · simpa only [headDeltaInput, if_pos hij, Rat.cast_one] using point_sound 1
  · simpa only [headDeltaInput, if_neg hij, Rat.cast_zero] using point_sound 0

def headHouseholderInput (digits : ℕ) (e a : Fin 31 → Interval) (den : Interval) :
    Matrix (Fin 31) (Fin 31) Interval := fun i j =>
  intervalSubtract (headDeltaInput i j)
    (roundedPositiveDivide digits
      (roundInterval digits (mul (add (e i) (a i)) (add (e j) (a j)))) den)

theorem head_householder_input_sound (digits : ℕ) (e a : Fin 31 → Interval) (den : Interval)
    (v w : Fin 31 → ℝ) (he : ∀ i, Contains (e i) (v i)) (ha : ∀ i, Contains (a i) (w i))
    (hd : Contains den (1+∑ r, v r*w r)) (hpos : 0 < den.lo) :
    MatrixContains (headHouseholderInput digits e a den) (realHeadHouseholder v w) := by
  intro i j
  have hn := roundInterval_sound digits _ _
    (mul_sound _ _ _ _ (add_sound _ _ _ _ (he i) (ha i)) (add_sound _ _ _ _ (he j) (ha j)))
  have hq := rounded_positive_divide_sound digits _ _ _ _ hpos hn hd
  have h := interval_subtract_sound _ _ _ _ (head_delta_input_sound i j) hq
  have heq : (if i = j then (1:ℝ) else 0)-(v i+w i)*(v j+w j)/(1+∑ r, v r*w r) =
      realHeadHouseholder v w i j := by
    unfold realHeadHouseholder
    rw [div_eq_mul_inv]
    ring
  rw [heq] at h
  exact h

def headNeutralInput (digits : ℕ) (e p : Fin 31 → Interval) :
    Matrix (Fin 31) (Fin 31) Interval := fun i j =>
  add (headDeltaInput i j) (roundInterval digits (mul (e i) (intervalSubtract (p j) (e j))))

def headNeutralInvInput (digits : ℕ) (e p : Fin 31 → Interval) :
    Matrix (Fin 31) (Fin 31) Interval := fun i j =>
  intervalSubtract (headDeltaInput i j)
    (roundInterval digits (mul (e i) (intervalSubtract (p j) (e j))))

theorem head_neutral_input_sound (digits : ℕ) (e p : Fin 31 → Interval) (v w : Fin 31 → ℝ)
    (he : ∀ i, Contains (e i) (v i)) (hp : ∀ i, Contains (p i) (w i)) :
    MatrixContains (headNeutralInput digits e p) (realHeadNeutral v w) := by
  intro i j
  exact add_sound _ _ _ _ (head_delta_input_sound i j)
    (roundInterval_sound digits _ _ (mul_sound _ _ _ _ (he i)
      (interval_subtract_sound _ _ _ _ (hp j) (he j))))

theorem head_neutral_inv_input_sound (digits : ℕ) (e p : Fin 31 → Interval) (v w : Fin 31 → ℝ)
    (he : ∀ i, Contains (e i) (v i)) (hp : ∀ i, Contains (p i) (w i)) :
    MatrixContains (headNeutralInvInput digits e p) (realHeadNeutralInv v w) := by
  intro i j
  exact interval_subtract_sound _ _ _ _ (head_delta_input_sound i j)
    (roundInterval_sound digits _ _ (mul_sound _ _ _ _ (he i)
      (interval_subtract_sound _ _ _ _ (hp j) (he j))))

def headAnchorProjectionInput (digits : ℕ) (a : Fin 31 → Interval) :
    Matrix (Fin 31) (Fin 31) Interval := fun i j => roundInterval digits (mul (a i) (a j))

theorem head_anchor_projection_input_sound (digits : ℕ) (a : Fin 31 → Interval)
    (v : Fin 31 → ℝ) (ha : ∀ i, Contains (a i) (v i)) :
    MatrixContains (headAnchorProjectionInput digits a) (fun i j => v i*v j) := by
  intro i j
  exact roundInterval_sound digits _ _ (mul_sound _ _ _ _ (ha i) (ha j))

def finiteHouseholderInput : Matrix (Fin 31) (Fin 31) Interval :=
  headHouseholderInput 30 finiteRotationInput finiteAnchorInput finiteHouseholderDenInput
def finiteNeutralInput : Matrix (Fin 31) (Fin 31) Interval :=
  headNeutralInput 30 finiteRotationInput finiteAdjointInput
def finiteNeutralInvInput : Matrix (Fin 31) (Fin 31) Interval :=
  headNeutralInvInput 30 finiteRotationInput finiteAdjointInput
def finiteAnchorProjectionInput : Matrix (Fin 31) (Fin 31) Interval :=
  headAnchorProjectionInput 30 finiteAnchorInput

theorem finite_householder_input_sound : MatrixContains finiteHouseholderInput realFiniteHouseholder :=
  head_householder_input_sound 30 _ _ _ _ _ finite_rotation_input_sound finite_anchor_input_sound
    finite_householder_den_input_sound finite_householder_den_input_pos

theorem finite_neutral_input_sound : MatrixContains finiteNeutralInput realFiniteNeutral :=
  head_neutral_input_sound 30 _ _ _ _ finite_rotation_input_sound finite_adjoint_input_sound

theorem finite_neutral_inv_input_sound : MatrixContains finiteNeutralInvInput realFiniteNeutralInv :=
  head_neutral_inv_input_sound 30 _ _ _ _ finite_rotation_input_sound finite_adjoint_input_sound

theorem finite_anchor_projection_input_sound :
    MatrixContains finiteAnchorProjectionInput realFiniteAnchorProjection :=
  head_anchor_projection_input_sound 30 _ _ finite_anchor_input_sound

end Lemniscate.CoarseArithmetic
