import Lemniscate.PeriodicCosineSpace

/-! Fourier coefficients of the infinite L2 cosine synthesis. These identities
verify the frequency support and normalization after taking the infinite sum. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

theorem circle_even_cosine_coeff_hasSum (v : CosineSequenceSpace) (n : ℤ) :
    HasSum (fun j : ℕ => v j * fourierCoeff (circleEvenCosineMode T j) n)
      (fourierCoeff (circleEvenCosineSynthesis T v) n) := by
  have h := (circle_even_cosine_hasSum T v).mapL
    (innerSL ℂ (fourierBasis (T := T) n))
  simpa only [innerSL_apply_apply, inner_smul_right,
    ← HilbertBasis.repr_apply_apply, fourierBasis_repr] using h

theorem circle_even_cosine_coeff_eq_tsum (v : CosineSequenceSpace) (n : ℤ) :
    fourierCoeff (circleEvenCosineSynthesis T v) n =
      ∑' j : ℕ, v j * fourierCoeff (circleEvenCosineMode T j) n :=
  (circle_even_cosine_coeff_hasSum T v n).tsum_eq.symm

theorem circle_even_cosine_mode_coeff_zero (j : ℕ) :
    fourierCoeff (circleEvenCosineMode T j) 0 = if j = 0 then 1 else 0 := by
  rw [circle_even_cosine_mode_coeff]
  by_cases hj : j = 0
  · simp [hj]
  · have hp : (0:ℤ) ≠ 2*(j:ℤ) := by omega
    have hn : (0:ℤ) ≠ -(2*(j:ℤ)) := by omega
    simp [hj, hp, hn]

theorem circle_even_cosine_coeff_zero (v : CosineSequenceSpace) :
    fourierCoeff (circleEvenCosineSynthesis T v) 0 = v 0 := by
  rw [circle_even_cosine_coeff_eq_tsum]
  simp only [circle_even_cosine_mode_coeff_zero, mul_ite, mul_one, mul_zero]
  simp

theorem circle_even_cosine_mode_coeff_pos (j k : ℕ) (hj : 0 < j) :
    fourierCoeff (circleEvenCosineMode T k) (2*(j:ℤ)) =
      if k = j then evenCosineFactor else 0 := by
  rw [circle_even_cosine_mode_coeff]
  have hn : 2*(j:ℤ) ≠ -(2*(k:ℤ)) := by omega
  have hz : 2*(j:ℤ) ≠ 0 := by omega
  by_cases hk : k = 0
  · simp [hk, hz, Ne.symm (Nat.ne_of_gt hj)]
  · by_cases he : k = j
    · subst k
      simp [hk, hn]
    · have hp : 2*(j:ℤ) ≠ 2*(k:ℤ) := by omega
      simp [hk, he, hp, hn]

theorem circle_even_cosine_coeff_pos (v : CosineSequenceSpace) (j : ℕ) (hj : 0 < j) :
    fourierCoeff (circleEvenCosineSynthesis T v) (2*(j:ℤ)) = v j * evenCosineFactor := by
  rw [circle_even_cosine_coeff_eq_tsum]
  simp only [circle_even_cosine_mode_coeff_pos T j _ hj, mul_ite, mul_zero]
  simp

theorem circle_even_cosine_mode_coeff_neg (j : ℕ) (n : ℤ) :
    fourierCoeff (circleEvenCosineMode T j) (-n) =
      fourierCoeff (circleEvenCosineMode T j) n := by
  simp only [circle_even_cosine_mode_coeff, neg_eq_iff_eq_neg, neg_neg, neg_zero]
  by_cases hj : j = 0
  · simp [hj]
  · simp only [if_neg hj]
    rw [add_comm]

theorem circle_even_cosine_coeff_neg (v : CosineSequenceSpace) (n : ℤ) :
    fourierCoeff (circleEvenCosineSynthesis T v) (-n) =
      fourierCoeff (circleEvenCosineSynthesis T v) n := by
  simp only [circle_even_cosine_coeff_eq_tsum, circle_even_cosine_mode_coeff_neg]

theorem circle_even_cosine_mode_coeff_odd (j : ℕ) (n : ℤ) :
    fourierCoeff (circleEvenCosineMode T j) (2*n+1) = 0 := by
  have hz : 2*n+1 ≠ 0 := by omega
  have hp : 2*n+1 ≠ 2*(j:ℤ) := by omega
  have hn : 2*n+1 ≠ -(2*(j:ℤ)) := by omega
  simp [circle_even_cosine_mode_coeff, hz, hp, hn]

theorem circle_even_cosine_coeff_odd (v : CosineSequenceSpace) (n : ℤ) :
    fourierCoeff (circleEvenCosineSynthesis T v) (2*n+1) = 0 := by
  simp only [circle_even_cosine_coeff_eq_tsum, circle_even_cosine_mode_coeff_odd,
    mul_zero, tsum_zero]

end Lemniscate
