import Lemniscate.PeriodicCosineMatrix

/-! Connect the actual mode matrix to the coefficient matrix used in the
arithmetic estimates. The coefficient identification and period relation remain
explicit hypotheses: this does not assert the missing Jacobi/theta identity. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic

variable (T : ℝ) [Fact (0 < T)]

theorem circle_even_coefficient_difference (h : C(AddCircle T, ℂ)) (r q : ℝ)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient r q j:ℂ)) (j k : ℕ) :
    fourierCoeff h (2*(j:ℤ)-2*(k:ℤ)) = (fourierCoefficient r q (j-k+(k-j)):ℂ) := by
  by_cases hkj : k ≤ j
  · have hi : 2*(j:ℤ)-2*(k:ℤ) = 2*((j-k:ℕ):ℤ) := by omega
    rw [hi, hc, Nat.sub_eq_zero_of_le hkj, Nat.add_zero]
  · have hjk : j ≤ k := by omega
    have hi : 2*(j:ℤ)-2*(k:ℤ) = -(2*((k-j:ℕ):ℤ)) := by omega
    rw [hi, hs, hc, Nat.sub_eq_zero_of_le hjk, Nat.zero_add]

theorem circle_even_coefficient_sum (h : C(AddCircle T, ℂ)) (r q : ℝ)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient r q j:ℂ)) (j k : ℕ) :
    fourierCoeff h (2*(j:ℤ)+2*(k:ℤ)) = (fourierCoefficient r q (j+k):ℂ) := by
  rw [show 2*(j:ℤ)+2*(k:ℤ) = 2*((j+k:ℕ):ℤ) by omega, hc]

theorem circle_cosine_matrix_eq_coefficients (h h₁ h₂ : C(AddCircle T, ℂ)) (r q : ℝ)
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient r q j:ℂ))
    (hr : (2*Real.pi/T)^2 = r) (j k : ℕ) :
    inner ℂ (circleEvenCosineMode T j)
      (circleContinuousL2 T (circleSymmetricCosineMode T h h₁ h₂ k)) =
        (cosineMatrixEntry r q j k:ℂ) := by
  by_cases hj : j = 0
  · subst j
    by_cases hk : k = 0
    · subst k
      rw [circle_cosine_matrix_zero_zero T h h₁ h₂ hh hh₁]
      simp [cosineMatrixEntry]
    · rw [circle_cosine_matrix_zero_positive T h h₁ h₂ hh hh₁ hs k (Nat.pos_of_ne_zero hk),
        hc, hr]
      simp only [cosineMatrixEntry, hk, and_false, if_false, true_or, if_true,
        Nat.zero_add, Nat.cast_zero, zero_mul, zero_add]
      push_cast
      ring
  · by_cases hk : k = 0
    · subst k
      rw [circle_cosine_matrix_positive_zero T h h₁ h₂ hh hh₁ hs j (Nat.pos_of_ne_zero hj),
        hc, hr]
      simp only [cosineMatrixEntry, hj, false_and, if_false, or_true, if_true,
        Nat.add_zero, Nat.cast_zero, zero_mul, add_zero]
      push_cast
      ring
    · rw [circle_cosine_matrix_positive T h h₁ h₂ hh hh₁ hs j k
        (Nat.pos_of_ne_zero hj) (Nat.pos_of_ne_zero hk),
        circle_even_coefficient_difference T h r q hs hc,
        circle_even_coefficient_sum T h r q hc, hr]
      have hr₄ : (2*Real.pi/T)^4 = r^2 := by
        calc
          _ = ((2*Real.pi/T)^2)^2 := by ring
          _ = _ := by rw [hr]
      rw [hr₄]
      simp only [cosineMatrixEntry, hj, hk, false_and, false_or, if_false]
      by_cases he : j = k
      · simp only [if_pos he]
        rw [he]
        push_cast
        ring
      · simp only [if_neg he]
        push_cast
        ring

end Lemniscate
