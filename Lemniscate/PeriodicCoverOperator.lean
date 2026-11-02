import Lemniscate.PeriodicCoverH4
import Lemniscate.PeriodicCoverMultiplication

/-! Intertwining of the actual long-period operator and the short-period
Bloch operator. Only the periodic extension data for the original coefficient
are assumed; those for its two derivatives follow from differentiation. -/
namespace Lemniscate
open Complex MeasureTheory
variable (T S : ℝ) [Fact (0 < T)] [Fact (0 < S)]

private theorem cover_derivative_coefficients (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T)
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

theorem circle_cover_operator_intertwine (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T)
    (h h₁ h₂ : C(AddCircle T, ℂ)) (H H₁ H₂ : C(AddCircle S, ℂ))
    (hd : HasCircleDeriv T h h₁) (hd₁ : HasCircleDeriv T h₁ h₂)
    (hD : HasCircleDeriv S H H₁) (hD₁ : HasCircleDeriv S H₁ H₂)
    (hmulti : ∀ n : ℤ, fourierCoeff H ((M:ℤ)*n) = fourierCoeff h n)
    (hvanish : ∀ n : ℤ, ¬(M:ℤ) ∣ n → fourierCoeff H n = 0)
    (j : ℤ) (f : circleH4Domain S) :
    circleCoverComponent T S M hM j (circleH4Operator S H H₁ H₂ f) =
      circleBlochOperator T h h₁ h₂ ((j:ℝ)/(M:ℝ)) (circleCoverComponentH4 T S M hM hS j f) := by
  obtain ⟨hmulti₁,hvanish₁⟩ := cover_derivative_coefficients T S M hM hS h h₁ H H₁ hd hD hmulti hvanish
  obtain ⟨hmulti₂,hvanish₂⟩ := cover_derivative_coefficients T S M hM hS h₁ h₂ H₁ H₂ hd₁ hD₁ hmulti₁ hvanish₁
  simp only [circle_h4_operator_expanded,circleBlochOperator,
    LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.comp_apply,
    Submodule.subtype_apply,map_add,map_sub,map_smul,
    circle_cover_shifted_first,circle_cover_shifted_second,circle_cover_shifted_fourth,
    circle_cover_component_h4_coe,
    circle_cover_multiply T S M hM h H hmulti hvanish,
    circle_cover_multiply T S M hM h₁ H₁ hmulti₁ hvanish₁,
    circle_cover_multiply T S M hM h₂ H₂ hmulti₂ hvanish₂]
  rfl

end Lemniscate
