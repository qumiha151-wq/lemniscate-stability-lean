import Lemniscate.PeriodicMultiplication

/-! Identify the classical fourth-order energy with the form involving only
two derivatives. All integration by parts is on the actual periodic L2 space. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic

variable (T : ℝ) [Fact (0 < T)]

theorem circle_classical_weak_deriv (f f₁ : C(AddCircle T, ℂ))
    (hf : HasCircleDeriv T f f₁) :
    HasWeakCircleDeriv T (circleContinuousL2 T f) (circleContinuousL2 T f₁) := by
  apply weak_circle_deriv_of_fourier
  intro n
  simpa only [circle_continuous_l2_fourier] using fourierCoeff_classical_deriv T f f₁ hf n

theorem circle_classical_integration_by_parts (f f₁ g g₁ : C(AddCircle T, ℂ))
    (hf : HasCircleDeriv T f f₁) (hg : HasCircleDeriv T g g₁) :
    inner ℂ (circleContinuousL2 T f₁) (circleContinuousL2 T g) =
      -inner ℂ (circleContinuousL2 T f) (circleContinuousL2 T g₁) :=
  circle_classical_weak_deriv T f f₁ hf g g₁ hg

theorem circle_weak_integration_by_parts (f f₁ g g₁ : CircleL2 T)
    (hf : HasWeakCircleDeriv T f f₁) (hg : HasWeakCircleDeriv T g g₁) :
    inner ℂ f₁ g = -inner ℂ f g₁ := by
  have hi := circle_complex_multiplier_duality T f f₁ g ((-1:ℂ) • g₁)
    (circleFrequencyFactor T) (fourier_of_weak_circle_deriv T f f₁ hf) (by
      intro n
      rw [circle_fourierCoeff_smul, fourier_of_weak_circle_deriv T g g₁ hg,
        circle_frequency_factor_conj]
      ring)
  simpa only [inner_smul_right, neg_one_mul] using hi

theorem circle_deriv_mul (f f₁ g g₁ : C(AddCircle T, ℂ))
    (hf : HasCircleDeriv T f f₁) (hg : HasCircleDeriv T g g₁) :
    HasCircleDeriv T (f*g) (f₁*g+f*g₁) := by
  intro x
  exact (hf x).mul (hg x)

theorem circle_classical_energy_eq (h h₁ h₂ f f₁ f₂ f₃ f₄ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hf : HasCircleDeriv T f f₁)
    (hf₁ : HasCircleDeriv T f₁ f₂) (hf₂ : HasCircleDeriv T f₂ f₃)
    (hf₃ : HasCircleDeriv T f₃ f₄) :
    (inner ℂ (circleContinuousL2 T f)
      (circleContinuousL2 T (circleSymmetricExpression T h h₁ h₂ f f₁ f₂ f₄))).re =
      circleH2Energy T h h₂ (circleContinuousL2 T f) (circleContinuousL2 T f₁)
        (circleContinuousL2 T f₂) := by
  have hfourth : inner ℂ (circleContinuousL2 T f) (circleContinuousL2 T f₄) =
      inner ℂ (circleContinuousL2 T f₂) (circleContinuousL2 T f₂) := by
    have ha := circle_classical_integration_by_parts T f f₁ f₃ f₄ hf hf₃
    have hb := circle_classical_integration_by_parts T f₁ f₂ f₂ f₃ hf₁ hf₂
    rw [ha, neg_neg] at hb
    exact hb.symm
  have hd := circle_classical_integration_by_parts T f f₁ (h*f₁) (h₁*f₁+h*f₂) hf
    (circle_deriv_mul T h h₁ f₁ f₂ hh hf₁)
  have hdiv : inner ℂ (circleContinuousL2 T f) (circleContinuousL2 T (h₁*f₁+h*f₂)) =
      -inner ℂ (circleContinuousL2 T f₁) (circleContinuousL2 T (h*f₁)) :=
    neg_eq_iff_eq_neg.mp hd.symm
  have hl : circleContinuousL2 T (circleSymmetricExpression T h h₁ h₂ f f₁ f₂ f₄) =
      (-4:ℂ) • circleContinuousL2 T f₄ - (45:ℂ) • circleContinuousL2 T (h₁*f₁+h*f₂) -
        (42:ℂ) • circleContinuousL2 T f + (15/4:ℂ) • circleContinuousL2 T (h₂*f) := by
    simp only [circleSymmetricExpression, circleContinuousL2, map_add, map_sub, map_smul]
  unfold circleH2Energy
  apply congrArg Complex.re
  rw [hl]
  simp only [inner_add_right, inner_sub_right, inner_smul_right]
  rw [hfourth, hdiv, ← circle_multiply_l2_continuous, ← circle_multiply_l2_continuous]
  ring

theorem circle_polynomial_h2_energy_eq (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (I : Finset ℕ) (v : ℕ → ℂ) :
    circleH2Energy T h h₂ (circleContinuousL2 T (circleCosinePolynomial T I v 0))
      (circleContinuousL2 T (circleCosinePolynomial T I v 1))
      (circleContinuousL2 T (circleCosinePolynomial T I v 2)) =
      (inner ℂ (circleContinuousL2 T (circleCosinePolynomial T I v 0))
        (circleContinuousL2 T (circleSymmetricPolynomial T h h₁ h₂ I v))).re := by
  exact (circle_classical_energy_eq T h h₁ h₂
    (circleCosinePolynomial T I v 0) (circleCosinePolynomial T I v 1)
    (circleCosinePolynomial T I v 2) (circleCosinePolynomial T I v 3)
    (circleCosinePolynomial T I v 4) hh
    (circle_cosine_polynomial_deriv T I v 0) (circle_cosine_polynomial_deriv T I v 1)
    (circle_cosine_polynomial_deriv T I v 2) (circle_cosine_polynomial_deriv T I v 3)).symm

theorem circle_polynomial_h2_energy_dissipative (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (I : Finset ℕ) (v : ℕ → ℂ) :
    circleH2Energy T h h₂ (circleContinuousL2 T (circleCosinePolynomial T I v 0))
      (circleContinuousL2 T (circleCosinePolynomial T I v 1))
      (circleContinuousL2 T (circleCosinePolynomial T I v 2)) ≤
      -(21/4:ℝ)*‖circleContinuousL2 T (circleCosinePolynomial T I v 0)‖^2 := by
  rw [circle_polynomial_h2_energy_eq T h h₁ h₂ hh]
  exact circle_polynomial_dissipative T h h₁ h₂ hh hh₁ hs hc hr I v

end Lemniscate
