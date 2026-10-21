import Lemniscate.PeriodicSineTail

/-! Fourier coefficients of the sine tail and the first-mode/tail decomposition. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic

variable (T : ℝ) [Fact (0 < T)]

theorem circle_sine_tail_coeff_hasSum (v : SineTailSpace) (n : ℤ) :
    HasSum (fun j : ℕ => v j*fourierCoeff (circleEvenSineMode T (j+1)) n)
      (fourierCoeff (circleSineTailSynthesis T v) n) := by
  have h := (circle_sine_tail_hasSum T v).mapL (innerSL ℂ (fourierBasis (T := T) n))
  simpa only [innerSL_apply_apply, inner_smul_right,
    ← HilbertBasis.repr_apply_apply, fourierBasis_repr] using h

theorem circle_sine_tail_coeff_eq_tsum (v : SineTailSpace) (n : ℤ) :
    fourierCoeff (circleSineTailSynthesis T v) n =
      ∑' j : ℕ, v j*fourierCoeff (circleEvenSineMode T (j+1)) n :=
  (circle_sine_tail_coeff_hasSum T v n).tsum_eq.symm

theorem circle_sine_tail_coeff_first (v : SineTailSpace) :
    fourierCoeff (circleSineTailSynthesis T v) 2 = 0 := by
  have h (j : ℕ) : fourierCoeff (circleEvenSineMode T (j+1)) 2 = 0 := by
    simpa using circle_even_sine_mode_coeff_pos T 0 (j+1)
  simp only [circle_sine_tail_coeff_eq_tsum, h, mul_zero, tsum_zero]

theorem circle_sine_tail_coeff_pos (v : SineTailSpace) (j : ℕ) :
    fourierCoeff (circleSineTailSynthesis T v) (2*((j+2:ℕ):ℤ)) = v j*evenSineFactor := by
  rw [circle_sine_tail_coeff_eq_tsum]
  have h (k : ℕ) : fourierCoeff (circleEvenSineMode T (k+1)) (2*((j+2:ℕ):ℤ)) =
      if k = j then evenSineFactor else 0 := by
    simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.add_left_inj] using
      circle_even_sine_mode_coeff_pos T (j+1) (k+1)
  simp only [h, mul_ite, mul_zero]
  simp

theorem circle_sine_tail_coeff_zero (v : SineTailSpace) :
    fourierCoeff (circleSineTailSynthesis T v) 0 = 0 := by
  simp only [circle_sine_tail_coeff_eq_tsum, circle_even_sine_mode_coeff_zero, mul_zero, tsum_zero]

theorem circle_sine_tail_coeff_neg (v : SineTailSpace) (n : ℤ) :
    fourierCoeff (circleSineTailSynthesis T v) (-n) =
      -fourierCoeff (circleSineTailSynthesis T v) n := by
  simp only [circle_sine_tail_coeff_eq_tsum, circle_even_sine_mode_coeff_neg, mul_neg, tsum_neg]

theorem circle_sine_tail_coeff_odd (v : SineTailSpace) (n : ℤ) :
    fourierCoeff (circleSineTailSynthesis T v) (2*n+1) = 0 := by
  simp only [circle_sine_tail_coeff_eq_tsum, circle_even_sine_mode_coeff_odd, mul_zero, tsum_zero]

end Lemniscate
