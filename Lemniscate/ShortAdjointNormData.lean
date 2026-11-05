import Lemniscate.ShortSchurInputs

/-! Small finite norm comparisons for the actual new e7 and psi7 inputs.
Only exact rational interval arithmetic is evaluated by the kernel. -/
namespace Lemniscate.CoarseArithmetic
open Finset

def shortSevenSquareInput (v : Fin 7 → Interval) (w : Fin 7 → ℚ) : Interval :=
  ⟨∑ i : Fin 7, (scale (mul (v i) (v i)) (w i)).lo,
    ∑ i : Fin 7, (scale (mul (v i) (v i)) (w i)).hi⟩

def shortVWeight (i : Fin 7) : ℚ := (2*(i.val+1))^4
def shortH1Weight (i : Fin 7) : ℚ := 1+(2*(i.val+1))^2

def shortShiftedRotationInput (i : Fin 7) : Interval :=
  add (shortRotationSineInput i) (point (if i=0 then 1 else 0))

def shortAdjointDifferenceInput (i : Fin 7) : Interval :=
  add (shortAdjointSineInput i) (scale (shortRotationSineInput i) (-1))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem short_seven_norm_certificate :
    (shortSevenSquareInput shortRotationSineInput shortVWeight).hi < 25 ∧
    (shortSevenSquareInput shortAdjointSineInput (fun _ => 1)).hi < 4 ∧
    (shortSevenSquareInput shortAdjointSineInput shortH1Weight).hi < 9 ∧
    (shortSevenSquareInput shortAdjointDifferenceInput (fun _ => 1)).hi < (1/20:ℚ)^2 ∧
    (shortSevenSquareInput shortAdjointDifferenceInput shortH1Weight).hi < (11/50:ℚ)^2 ∧
    (shortSevenSquareInput shortShiftedRotationInput shortVWeight).hi < (849/100:ℚ)^2 ∧
    (shortSevenSquareInput shortShiftedRotationInput (fun i => 1/shortVWeight i)).hi < (499/1000:ℚ)^2 ∧
    (shortSevenSquareInput shortShiftedRotationInput shortH1Weight).hi < (4499/1000:ℚ)^2 ∧
    (shortSevenSquareInput shortShiftedRotationInput (fun i => 1/shortH1Weight i)).hi < (889/1000:ℚ)^2 ∧
    (1981/1000:ℚ) < (shortShiftedRotationInput 0).lo := by decide +kernel

theorem short_seven_square_input_sound (v : Fin 7 → Interval)
    (x : Fin 7 → ℝ) (w : Fin 7 → ℚ) (hx : ∀ i, Contains (v i) (x i)) :
    Contains (shortSevenSquareInput v w) (∑ i : Fin 7, (w i:ℝ)*(x i)^2) := by
  have h (i : Fin 7) := scale_sound _ _ (w i)
    (mul_sound _ _ _ _ (hx i) (hx i))
  have hs : Contains (shortSevenSquareInput v w)
      (∑ i : Fin 7, (x i*x i)*(w i:ℝ)) := by
    simpa only [shortSevenSquareInput] using sum_interval_sound
      (fun i : Fin 7 => scale (mul (v i) (v i)) (w i))
      (fun i : Fin 7 => (x i*x i)*(w i:ℝ)) h
  have he : (∑ i : Fin 7, (w i:ℝ)*(x i)^2) =
      ∑ i : Fin 7, (x i*x i)*(w i:ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  exact hs

theorem short_seven_square_bound (v : Fin 7 → Interval)
    (x : Fin 7 → ℝ) (w : Fin 7 → ℚ) (B : ℚ)
    (hx : ∀ i, Contains (v i) (x i))
    (hB : (shortSevenSquareInput v w).hi < B) :
    (∑ i : Fin 7, (w i:ℝ)*(x i)^2) < (B:ℝ) :=
  (short_seven_square_input_sound v x w hx).2.trans_lt (Rat.cast_lt.mpr hB)

theorem short_shifted_rotation_input_sound (i : Fin 7) :
    Contains (shortShiftedRotationInput i)
      (shortRotationSine shortActualCoefficient i + if i=0 then 1 else 0) := by
  have hp : Contains (point (if i=0 then 1 else 0))
      (if i=0 then (1:ℝ) else 0) := by
    by_cases hi : i=0 <;> simp only [hi,if_true,if_false]
    · simpa only [Rat.cast_one] using point_sound 1
    · simpa only [Rat.cast_zero] using point_sound 0
  exact add_sound _ _ _ _ (short_rotation_sine_input_sound i) hp

theorem short_adjoint_difference_input_sound (i : Fin 7) :
    Contains (shortAdjointDifferenceInput i)
      (shortAdjointSine shortActualCoefficient i-shortRotationSine shortActualCoefficient i) := by
  have h := add_sound _ _ _ _ (short_adjoint_sine_input_sound i)
    (scale_sound _ _ (-1) (short_rotation_sine_input_sound i))
  simpa only [shortAdjointDifferenceInput,Rat.cast_neg,Rat.cast_one,
    mul_neg_one,sub_eq_add_neg] using h

end Lemniscate.CoarseArithmetic
