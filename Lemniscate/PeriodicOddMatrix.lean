import Lemniscate.OddMatrix
import Lemniscate.PeriodicMatrixIdentification

/-! Identification of the zero-parameter odd-index matrix with actual periodic
Fourier-mode pairings. The concrete profile Fourier data and period identity
remain explicit hypotheses; no Bloch operator identity is assumed proved here. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic OddArithmetic

variable (T : ℝ) [Fact (0 < T)]

theorem circle_even_integer_coefficient (h : C(AddCircle T, ℂ)) (r q : ℝ)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient r q j:ℂ)) (k : ℤ) :
    fourierCoeff h (2*k) = (fourierCoefficient r q k.natAbs:ℂ) := by
  cases k with
  | ofNat k => exact hc k
  | negSucc k =>
    have he : 2*Int.negSucc k = -(2*((k+1:ℕ):ℤ)) := by omega
    rw [he, hs, hc]
    rfl

theorem circle_odd_difference_coefficient (h : C(AddCircle T, ℂ)) (r q : ℝ)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient r q j:ℂ))
    (n m : ℤ) (hn : Odd n) (hm : Odd m) :
    fourierCoeff h (n-m) = (fourierCoefficient r q ((n-m).natAbs/2):ℂ) := by
  rcases hn with ⟨j, hj⟩
  rcases hm with ⟨k, hk⟩
  have he : n-m = 2*(j-k) := by omega
  rw [he, circle_even_integer_coefficient T h r q hs hc]
  simp [Int.natAbs_mul]

theorem circle_odd_matrix_entry (h : C(AddCircle T, ℂ))
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (n m : ℤ) (hn : Odd n) (hm : Odd m) :
    circleSymmetricFourierEntry T h n m = (oddMatrixEntry 0 n m:ℂ) := by
  have hr4 : (2*Real.pi/T)^4 = thetaParameter^2 := by
    calc
      _ = ((2*Real.pi/T)^2)^2 := by ring
      _ = _ := by rw [hr]
  unfold circleSymmetricFourierEntry
  rw [hr, hr4, circle_odd_difference_coefficient T h thetaParameter nome hs hc n m hn hm]
  by_cases he : n = m
  · subst m
    simp only [oddMatrixEntry, ite_true, sub_self, Int.natAbs_zero, Nat.zero_div,
      add_zero, Int.cast_zero, sub_zero, mul_one]
    push_cast
    ring
  · simp only [oddMatrixEntry, if_neg he, oddEntryPolynomial, add_zero, mul_zero, zero_add]
    push_cast
    ring

theorem circle_odd_mode_pairing (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (n m : ℤ) (hn : Odd n) (hm : Odd m) :
    inner ℂ (fourierBasis (T := T) n) (circleContinuousL2 T (circleSymmetricMode T h h₁ h₂ m)) =
      (oddMatrixEntry 0 n m:ℂ) := by
  rw [← HilbertBasis.repr_apply_apply, fourierBasis_repr, circle_continuous_l2_fourier,
    circle_symmetric_mode_fourier T h h₁ h₂ hh hh₁,
    circle_odd_matrix_entry T h hs hc hr n m hn hm]

theorem circle_odd_mode_off_bound (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (n m : ℤ)
    (hn : Odd n) (hm : Odd m) (hne : n ≠ m) :
    ‖inner ℂ (fourierBasis (T := T) n)
      (circleContinuousL2 T (circleSymmetricMode T h h₁ h₂ m))‖ ≤
        realEval (absoluteEntryPolynomial n m) 0 := by
  rw [circle_odd_mode_pairing T h h₁ h₂ hh hh₁ hs hc hr n m hn hm,
    Complex.norm_real, Real.norm_eq_abs, oddMatrixEntry, if_neg hne]
  exact theta_nome_odd_off_diagonal_bound n m hn hm hne 0 (by norm_num) (by norm_num)

end Lemniscate
