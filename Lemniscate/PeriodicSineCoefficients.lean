import Lemniscate.PeriodicSineSpace

/-! Exact Fourier coefficients of the infinite sine synthesis, including
antisymmetry, normalization, the zero mode, and all odd modes. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

theorem circle_even_sine_coeff_hasSum (v : SineSequenceSpace) (n : ℤ) :
    HasSum (fun j : ℕ => v j*fourierCoeff (circleEvenSineMode T j) n)
      (fourierCoeff (circleEvenSineSynthesis T v) n) := by
  have h := (circle_even_sine_hasSum T v).mapL (innerSL ℂ (fourierBasis (T := T) n))
  simpa only [innerSL_apply_apply, inner_smul_right,
    ← HilbertBasis.repr_apply_apply, fourierBasis_repr] using h

theorem circle_even_sine_coeff_eq_tsum (v : SineSequenceSpace) (n : ℤ) :
    fourierCoeff (circleEvenSineSynthesis T v) n =
      ∑' j : ℕ, v j*fourierCoeff (circleEvenSineMode T j) n :=
  (circle_even_sine_coeff_hasSum T v n).tsum_eq.symm

theorem circle_even_sine_mode_coeff_zero (j : ℕ) :
    fourierCoeff (circleEvenSineMode T j) 0 = 0 := by
  have hp : (0:ℤ) ≠ 2*((j+1:ℕ):ℤ) := by omega
  have hn : (0:ℤ) ≠ -(2*((j+1:ℕ):ℤ)) := by omega
  simp only [circle_even_sine_mode_coeff, hp, hn, if_false, sub_self, mul_zero]

theorem circle_even_sine_coeff_zero (v : SineSequenceSpace) :
    fourierCoeff (circleEvenSineSynthesis T v) 0 = 0 := by
  simp only [circle_even_sine_coeff_eq_tsum, circle_even_sine_mode_coeff_zero, mul_zero, tsum_zero]

theorem circle_even_sine_mode_coeff_pos (j k : ℕ) :
    fourierCoeff (circleEvenSineMode T k) (2*((j+1:ℕ):ℤ)) =
      if k = j then evenSineFactor else 0 := by
  rw [circle_even_sine_mode_coeff]
  have hn : 2*((j+1:ℕ):ℤ) ≠ -(2*((k+1:ℕ):ℤ)) := by omega
  by_cases he : k = j
  · subst k; simp only [hn, if_false, if_true, sub_zero, mul_one]
  · have hp : 2*((j+1:ℕ):ℤ) ≠ 2*((k+1:ℕ):ℤ) := by omega
    simp only [he, hp, hn, if_false, sub_self, mul_zero]

theorem circle_even_sine_coeff_pos (v : SineSequenceSpace) (j : ℕ) :
    fourierCoeff (circleEvenSineSynthesis T v) (2*((j+1:ℕ):ℤ)) = v j*evenSineFactor := by
  rw [circle_even_sine_coeff_eq_tsum]
  simp only [circle_even_sine_mode_coeff_pos, mul_ite, mul_zero]
  simp

theorem circle_even_sine_mode_coeff_neg (j : ℕ) (n : ℤ) :
    fourierCoeff (circleEvenSineMode T j) (-n) = -fourierCoeff (circleEvenSineMode T j) n := by
  simp only [circle_even_sine_mode_coeff, neg_eq_iff_eq_neg, neg_neg]
  ring

theorem circle_even_sine_coeff_neg (v : SineSequenceSpace) (n : ℤ) :
    fourierCoeff (circleEvenSineSynthesis T v) (-n) =
      -fourierCoeff (circleEvenSineSynthesis T v) n := by
  simp only [circle_even_sine_coeff_eq_tsum, circle_even_sine_mode_coeff_neg, mul_neg, tsum_neg]

theorem circle_even_sine_mode_coeff_odd (j : ℕ) (n : ℤ) :
    fourierCoeff (circleEvenSineMode T j) (2*n+1) = 0 := by
  have hp : 2*n+1 ≠ 2*((j+1:ℕ):ℤ) := by omega
  have hn : 2*n+1 ≠ -(2*((j+1:ℕ):ℤ)) := by omega
  simp only [circle_even_sine_mode_coeff, hp, hn, if_false, sub_self, mul_zero]

theorem circle_even_sine_coeff_odd (v : SineSequenceSpace) (n : ℤ) :
    fourierCoeff (circleEvenSineSynthesis T v) (2*n+1) = 0 := by
  simp only [circle_even_sine_coeff_eq_tsum, circle_even_sine_mode_coeff_odd, mul_zero, tsum_zero]

end Lemniscate
