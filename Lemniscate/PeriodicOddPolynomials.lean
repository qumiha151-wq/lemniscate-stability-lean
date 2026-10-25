import Lemniscate.PeriodicOddMatrix
import Lemniscate.PeriodicIntegrationByParts
import Lemniscate.OddH2Dissipation

/-! Finite odd Fourier polynomials and their actual differential energy.
Every finite set of positive and negative odd frequencies is allowed. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic OddArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleOddPolynomial (I : Finset ℤ) (v : ℤ → ℂ) (k : ℕ) :
    C(AddCircle T, ℂ) :=
  ∑ j ∈ I, v j • ((circleFrequencyFactor T (2*j+1))^k • fourier (2*j+1))

theorem circle_odd_polynomial_deriv (I : Finset ℤ) (v : ℤ → ℂ) (k : ℕ) :
    HasCircleDeriv T (circleOddPolynomial T I v k) (circleOddPolynomial T I v (k+1)) := by
  intro x
  simpa only [circleOddPolynomial, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul] using HasDerivAt.fun_sum (u := I)
      (fun j _ => (circle_fourier_derivative_power T (2*j+1) k x).const_mul (v j))

theorem circle_odd_polynomial_l2 (I : Finset ℤ) (v : ℤ → ℂ) (k : ℕ) :
    circleContinuousL2 T (circleOddPolynomial T I v k) =
      ∑ j ∈ I, (v j*(circleFrequencyFactor T (2*j+1))^k) •
        fourierBasis (T := T) (2*j+1) := by
  calc
    _ = ∑ j ∈ I, (v j*(circleFrequencyFactor T (2*j+1))^k) •
        circleContinuousL2 T (fourier (2*j+1)) := by
      simp only [circleOddPolynomial, circleContinuousL2, map_sum, map_smul, smul_smul]
    _ = _ := by simp only [circle_continuous_l2_fourier_basis]

theorem circle_symmetric_expression_finset_sum {ι : Type*}
    (h h₁ h₂ : C(AddCircle T, ℂ)) (I : Finset ι)
    (f f₁ f₂ f₄ : ι → C(AddCircle T, ℂ)) :
    circleSymmetricExpression T h h₁ h₂ (∑ j ∈ I, f j) (∑ j ∈ I, f₁ j)
      (∑ j ∈ I, f₂ j) (∑ j ∈ I, f₄ j) =
        ∑ j ∈ I, circleSymmetricExpression T h h₁ h₂ (f j) (f₁ j) (f₂ j) (f₄ j) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [circleSymmetricExpression]
  | @insert j I hj ih =>
      simp only [Finset.sum_insert hj]
      rw [circle_symmetric_expression_add, ih]

noncomputable def circleSymmetricOddPolynomial (h h₁ h₂ : C(AddCircle T, ℂ))
    (I : Finset ℤ) (v : ℤ → ℂ) : C(AddCircle T, ℂ) :=
  circleSymmetricExpression T h h₁ h₂ (circleOddPolynomial T I v 0)
    (circleOddPolynomial T I v 1) (circleOddPolynomial T I v 2) (circleOddPolynomial T I v 4)

theorem circle_symmetric_odd_polynomial_sum (h h₁ h₂ : C(AddCircle T, ℂ))
    (I : Finset ℤ) (v : ℤ → ℂ) :
    circleSymmetricOddPolynomial T h h₁ h₂ I v =
      ∑ j ∈ I, v j • circleSymmetricMode T h h₁ h₂ (2*j+1) := by
  simp only [circleSymmetricOddPolynomial, circleOddPolynomial,
    circle_symmetric_expression_finset_sum, circle_symmetric_expression_smul,
    pow_zero, pow_one, one_smul, circleSymmetricMode]

theorem circle_odd_polynomial_energy_eq_matrix (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (I : Finset ℤ) (v : ℤ → ℂ) :
    inner ℂ (circleContinuousL2 T (circleOddPolynomial T I v 0))
      (circleContinuousL2 T (circleSymmetricOddPolynomial T h h₁ h₂ I v)) =
        ∑ i ∈ I, ∑ j ∈ I, oddEnergyTerm 0 v (i,j) := by
  rw [circle_odd_polynomial_l2, circle_symmetric_odd_polynomial_sum]
  simp only [pow_zero, mul_one, circleContinuousL2, map_sum, map_smul]
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [inner_smul_left, inner_smul_right]
  change conj (v i)*(v j*inner ℂ (fourierBasis (T := T) (2*i+1))
    (circleContinuousL2 T (circleSymmetricMode T h h₁ h₂ (2*j+1)))) = _
  rw [circle_odd_mode_pairing T h h₁ h₂ hh hh₁ hs hc hr _ _
    ⟨i, by ring⟩ ⟨j, by ring⟩]
  unfold oddEnergyTerm oddIndexedMatrix
  ring

theorem circle_odd_polynomial_h2_energy_eq (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (I : Finset ℤ) (v : ℤ → ℂ) :
    circleH2Energy T h h₂ (circleContinuousL2 T (circleOddPolynomial T I v 0))
      (circleContinuousL2 T (circleOddPolynomial T I v 1))
      (circleContinuousL2 T (circleOddPolynomial T I v 2)) =
      (inner ℂ (circleContinuousL2 T (circleOddPolynomial T I v 0))
        (circleContinuousL2 T (circleSymmetricOddPolynomial T h h₁ h₂ I v))).re := by
  exact (circle_classical_energy_eq T h h₁ h₂
    (circleOddPolynomial T I v 0) (circleOddPolynomial T I v 1)
    (circleOddPolynomial T I v 2) (circleOddPolynomial T I v 3)
    (circleOddPolynomial T I v 4) hh
    (circle_odd_polynomial_deriv T I v 0) (circle_odd_polynomial_deriv T I v 1)
    (circle_odd_polynomial_deriv T I v 2) (circle_odd_polynomial_deriv T I v 3)).symm

theorem circle_odd_polynomial_h2_energy_eq_coefficients (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (I : Finset ℤ) (v : ℤ → ℂ) :
    circleH2Energy T h h₂ (circleContinuousL2 T (circleOddPolynomial T I v 0))
      (circleContinuousL2 T (circleOddPolynomial T I v 1))
      (circleContinuousL2 T (circleOddPolynomial T I v 2)) =
        (∑ i ∈ I, ∑ j ∈ I, oddEnergyTerm 0 v (i,j)).re := by
  rw [circle_odd_polynomial_h2_energy_eq T h h₁ h₂ hh,
    circle_odd_polynomial_energy_eq_matrix T h h₁ h₂ hh hh₁ hs hc hr]

end Lemniscate
