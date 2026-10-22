import Lemniscate.PeriodicSineMatrix
import Lemniscate.PeriodicCosinePolynomials

/-! Actual smooth sine polynomials with the first mode separated from an
arbitrary finite tail. Their derivatives and operator action are computed. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleSinePolynomial (I : Finset ℕ) (u : ℂ) (v : ℕ → ℂ) (k : ℕ) :
    C(AddCircle T, ℂ) :=
  u • circleSineJet T 0 k + ∑ j ∈ I, v j • circleSineJet T (j+1) k

theorem circle_sine_polynomial_deriv (I : Finset ℕ) (u : ℂ) (v : ℕ → ℂ) (k : ℕ) :
    HasCircleDeriv T (circleSinePolynomial T I u v k)
      (circleSinePolynomial T I u v (k+1)) := by
  unfold circleSinePolynomial
  apply circle_deriv_add T
  · exact circle_deriv_smul T u _ _ (circle_sine_jet_deriv T 0 k)
  · intro x
    simpa only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul] using
      HasDerivAt.fun_sum (u := I)
        (fun j _ => (circle_sine_jet_deriv T (j+1) k x).const_mul (v j))

theorem circle_sine_polynomial_l2 (I : Finset ℕ) (u : ℂ) (v : ℕ → ℂ) :
    circleContinuousL2 T (circleSinePolynomial T I u v 0) =
      u • circleEvenSineMode T 0 + ∑ j ∈ I, v j • circleEvenSineMode T (j+1) := by
  simp only [circleSinePolynomial, circle_continuous_l2_add, circle_continuous_l2_sum,
    circle_continuous_l2_smul, circle_sine_jet_zero_l2]

noncomputable def circleSymmetricSinePolynomial (h h₁ h₂ : C(AddCircle T, ℂ))
    (I : Finset ℕ) (u : ℂ) (v : ℕ → ℂ) : C(AddCircle T, ℂ) :=
  circleSymmetricExpression T h h₁ h₂ (circleSinePolynomial T I u v 0)
    (circleSinePolynomial T I u v 1) (circleSinePolynomial T I u v 2)
    (circleSinePolynomial T I u v 4)

theorem circle_symmetric_sine_polynomial_sum (h h₁ h₂ : C(AddCircle T, ℂ))
    (I : Finset ℕ) (u : ℂ) (v : ℕ → ℂ) :
    circleSymmetricSinePolynomial T h h₁ h₂ I u v =
      u • circleSymmetricSineMode T h h₁ h₂ 0 +
        ∑ j ∈ I, v j • circleSymmetricSineMode T h h₁ h₂ (j+1) := by
  simp only [circleSymmetricSinePolynomial, circleSinePolynomial,
    circle_symmetric_expression_add, circle_symmetric_expression_sum,
    circle_symmetric_expression_smul, circleSymmetricSineMode]

theorem circle_symmetric_sine_polynomial_coordinate (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (I : Finset ℕ) (u : ℂ) (v : ℕ → ℂ) (x : ℝ) :
    circleSymmetricSinePolynomial T h h₁ h₂ I u v (x:AddCircle T) =
      -4*deriv (deriv (deriv (deriv
        (fun y : ℝ => circleSinePolynomial T I u v 0 (y:AddCircle T))))) x -
      45*deriv (fun y : ℝ => h (y:AddCircle T)*deriv
        (fun z : ℝ => circleSinePolynomial T I u v 0 (z:AddCircle T)) y) x -
      42*circleSinePolynomial T I u v 0 (x:AddCircle T) +
      (15/4:ℂ)*h₂ (x:AddCircle T)*circleSinePolynomial T I u v 0 (x:AddCircle T) := by
  exact circle_symmetric_expression_coordinate T h h₁ h₂
    (circleSinePolynomial T I u v 0) (circleSinePolynomial T I u v 1)
    (circleSinePolynomial T I u v 2) (circleSinePolynomial T I u v 3)
    (circleSinePolynomial T I u v 4) hh
    (circle_sine_polynomial_deriv T I u v 0) (circle_sine_polynomial_deriv T I u v 1)
    (circle_sine_polynomial_deriv T I u v 2) (circle_sine_polynomial_deriv T I u v 3) x

end Lemniscate
