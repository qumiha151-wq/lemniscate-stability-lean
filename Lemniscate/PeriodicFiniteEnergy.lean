import Lemniscate.PeriodicCosinePolynomials

/-! Transfer the certified finite matrix estimate to the actual differential
expression on finite cosine polynomials. Fourier/profile identification remains
an explicit analytic hypothesis, rather than an added axiom. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_symmetric_polynomial_coordinate (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (I : Finset ℕ) (v : ℕ → ℂ) (x : ℝ) :
    circleSymmetricPolynomial T h h₁ h₂ I v (x:AddCircle T) =
      -4*deriv (deriv (deriv (deriv
        (fun y : ℝ => circleCosinePolynomial T I v 0 (y:AddCircle T))))) x -
      45*deriv (fun y : ℝ => h (y:AddCircle T)*deriv
        (fun z : ℝ => circleCosinePolynomial T I v 0 (z:AddCircle T)) y) x -
      42*circleCosinePolynomial T I v 0 (x:AddCircle T) +
      (15/4:ℂ)*h₂ (x:AddCircle T)*circleCosinePolynomial T I v 0 (x:AddCircle T) := by
  exact circle_symmetric_expression_coordinate T h h₁ h₂
    (circleCosinePolynomial T I v 0) (circleCosinePolynomial T I v 1)
    (circleCosinePolynomial T I v 2) (circleCosinePolynomial T I v 3)
    (circleCosinePolynomial T I v 4) hh
    (circle_cosine_polynomial_deriv T I v 0) (circle_cosine_polynomial_deriv T I v 1)
    (circle_cosine_polynomial_deriv T I v 2) (circle_cosine_polynomial_deriv T I v 3) x

theorem circle_polynomial_energy_eq_matrix (h h₁ h₂ : C(AddCircle T, ℂ)) (r q : ℝ)
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient r q j:ℂ))
    (hr : (2*Real.pi/T)^2 = r) (I : Finset ℕ) (v : ℕ → ℂ) :
    inner ℂ (circleContinuousL2 T (circleCosinePolynomial T I v 0))
      (circleContinuousL2 T (circleSymmetricPolynomial T h h₁ h₂ I v)) =
      ∑ i ∈ I, ∑ j ∈ I, conj (v i)*(cosineMatrixEntry r q i j:ℂ)*v j := by
  rw [circle_cosine_polynomial_l2, circle_symmetric_polynomial_sum, circle_continuous_l2_sum]
  simp only [circle_continuous_l2_smul, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, circle_cosine_matrix_eq_coefficients T h h₁ h₂ r q
      hh hh₁ hs hc hr]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem circle_polynomial_dissipative (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (I : Finset ℕ) (v : ℕ → ℂ) :
    (inner ℂ (circleContinuousL2 T (circleCosinePolynomial T I v 0))
      (circleContinuousL2 T (circleSymmetricPolynomial T h h₁ h₂ I v))).re ≤
      -(21/4:ℝ)*‖circleContinuousL2 T (circleCosinePolynomial T I v 0)‖^2 := by
  rw [circle_polynomial_energy_eq_matrix T h h₁ h₂ thetaParameter nome hh hh₁ hs hc hr,
    circle_cosine_polynomial_norm_sq]
  exact cosine_finite_form_dissipative I v

end Lemniscate
