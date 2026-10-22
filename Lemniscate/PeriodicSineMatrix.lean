import Lemniscate.PeriodicSineJets
import Lemniscate.PeriodicMatrixIdentification
import Lemniscate.SineMatrix

/-! Identify the actual L2 sine matrix with the coefficient matrix used in the
certified inequalities. The complete profile/period identification is explicit. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_sine_matrix_pairing (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n) (j k : ℕ) :
    inner ℂ (circleEvenSineMode T j)
      (circleContinuousL2 T (circleSymmetricSineMode T h h₁ h₂ k)) =
        circleSymmetricFourierEntry T h (2*((j+1:ℕ):ℤ)) (2*((k+1:ℕ):ℤ)) -
        circleSymmetricFourierEntry T h (2*((j+1:ℕ):ℤ)) (-(2*((k+1:ℕ):ℤ))) := by
  rw [circle_sine_inner_fourier]
  simp only [circle_symmetric_sine_fourier T h h₁ h₂ hh hh₁]
  rw [circle_symmetric_entry_neg T h hs, circle_symmetric_entry_neg_left T h hs]
  calc
    _ = (conj evenSineFactor*(evenSineFactor*2))*
        (circleSymmetricFourierEntry T h (2*((j+1:ℕ):ℤ)) (2*((k+1:ℕ):ℤ)) -
          circleSymmetricFourierEntry T h (2*((j+1:ℕ):ℤ)) (-(2*((k+1:ℕ):ℤ)))) := by ring
    _ = _ := by rw [evenSineFactor_normalization, one_mul]

theorem circle_sine_matrix_positive (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n) (j k : ℕ) :
    inner ℂ (circleEvenSineMode T j)
      (circleContinuousL2 T (circleSymmetricSineMode T h h₁ h₂ k)) =
      ((-4*(2*Real.pi/T)^4*(2*((k+1:ℕ):ℝ))^4-42:ℝ):ℂ)*(if j = k then 1 else 0) +
      (((2*Real.pi/T)^2*(45*(2*((j+1:ℕ):ℝ))*(2*((k+1:ℕ):ℝ)) -
        (15/4:ℝ)*(2*((j+1:ℕ):ℝ)-2*((k+1:ℕ):ℝ))^2):ℝ):ℂ)*
          fourierCoeff h (2*((j+1:ℕ):ℤ)-2*((k+1:ℕ):ℤ)) +
      (((2*Real.pi/T)^2*(45*(2*((j+1:ℕ):ℝ))*(2*((k+1:ℕ):ℝ)) +
        (15/4:ℝ)*(2*((j+1:ℕ):ℝ)+2*((k+1:ℕ):ℝ))^2):ℝ):ℂ)*
          fourierCoeff h (2*((j+1:ℕ):ℤ)+2*((k+1:ℕ):ℤ)) := by
  rw [circle_sine_matrix_pairing T h h₁ h₂ hh hh₁ hs j k]
  have hcross : 2*((j+1:ℕ):ℤ) ≠ -(2*((k+1:ℕ):ℤ)) := by omega
  have heq : (2*((j+1:ℕ):ℤ) = 2*((k+1:ℕ):ℤ)) ↔ j = k := by omega
  unfold circleSymmetricFourierEntry
  simp only [if_neg hcross, heq, mul_zero, sub_neg_eq_add]
  push_cast
  ring

theorem circle_sine_matrix_eq_coefficients (h h₁ h₂ : C(AddCircle T, ℂ)) (r q : ℝ)
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient r q j:ℂ))
    (hr : (2*Real.pi/T)^2 = r) (j k : ℕ) :
    inner ℂ (circleEvenSineMode T j)
      (circleContinuousL2 T (circleSymmetricSineMode T h h₁ h₂ k)) =
        (sineMatrixEntry r q (j+1) (k+1):ℂ) := by
  rw [circle_sine_matrix_positive T h h₁ h₂ hh hh₁ hs j k,
    circle_even_coefficient_difference T h r q hs hc,
    circle_even_coefficient_sum T h r q hc, hr]
  have hr₄ : (2*Real.pi/T)^4 = r^2 := by
    calc
      _ = ((2*Real.pi/T)^2)^2 := by ring
      _ = _ := by rw [hr]
  rw [hr₄]
  simp only [sineMatrixEntry, Nat.add_left_inj]
  by_cases he : j = k
  · simp only [if_pos he]
    rw [he]
    push_cast
    ring
  · simp only [if_neg he]
    push_cast
    ring

end Lemniscate
