import Lemniscate.PeriodicCoverH4

/-! Periodic extension data for a coefficient pass to its derivative.
This lemma is shared by both directions of operator intertwining. -/
namespace Lemniscate
open Complex MeasureTheory
variable (T S : ℝ) [Fact (0 < T)] [Fact (0 < S)]

theorem circle_cover_derivative_coefficients (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T)
    (h h₁ : C(AddCircle T, ℂ)) (H H₁ : C(AddCircle S, ℂ))
    (hd : HasCircleDeriv T h h₁) (hD : HasCircleDeriv S H H₁)
    (hmulti : ∀ n : ℤ, fourierCoeff H ((M:ℤ)*n) = fourierCoeff h n)
    (hvanish : ∀ n : ℤ, ¬(M:ℤ) ∣ n → fourierCoeff H n = 0) :
    (∀ n : ℤ, fourierCoeff H₁ ((M:ℤ)*n) = fourierCoeff h₁ n) ∧
      (∀ n : ℤ, ¬(M:ℤ) ∣ n → fourierCoeff H₁ n = 0) := by
  constructor
  · intro n
    have hfreq : circleFrequencyFactor S ((M:ℤ)*n) = circleFrequencyFactor T n := by
      simpa [circleCoverIndex] using circle_cover_frequency T S M hM hS 0 n
    rw [fourierCoeff_classical_deriv S _ _ hD,fourierCoeff_classical_deriv T _ _ hd,
      hmulti,hfreq]
  · intro n hn
    rw [fourierCoeff_classical_deriv S _ _ hD,hvanish n hn,mul_zero]

end Lemniscate
