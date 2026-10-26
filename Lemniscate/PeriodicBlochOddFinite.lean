import Lemniscate.PeriodicBlochFourier
import Lemniscate.PeriodicOddApproximation

/-! Exact energy of finite odd Fourier sums for the actual Bloch operator.
Symmetrizing the pairing is sufficient; no separately realized symmetric
operator or basis-change matrix is needed. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic OddArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleOddPolynomialH4 (I : Finset ℤ) (v : ℤ → ℂ) : circleH4Domain T :=
  ∑ j ∈ I, v j • circleFourierH4 T (2*j+1)

theorem circle_odd_polynomial_h4_coe (I : Finset ℤ) (v : ℤ → ℂ) :
    (circleOddPolynomialH4 T I v : CircleL2 T) =
      circleContinuousL2 T (circleOddPolynomial T I v 0) := by
  rw [circle_odd_polynomial_l2]
  simp [circleOddPolynomialH4, circleFourierH4]

theorem circle_odd_polynomial_h4_symmetric_pairing (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (α : ℝ) (I : Finset ℤ) (v : ℤ → ℂ) :
    (inner ℂ (circleOddPolynomialH4 T I v : CircleL2 T)
        (circleBlochOperator T h h₁ h₂ α (circleOddPolynomialH4 T I v))+
      inner ℂ (circleBlochOperator T h h₁ h₂ α (circleOddPolynomialH4 T I v))
        (circleOddPolynomialH4 T I v : CircleL2 T))/2 =
      ∑ i ∈ I, ∑ j ∈ I, oddEnergyTerm α v (i,j) := by
  have hcoe : (circleOddPolynomialH4 T I v : CircleL2 T) =
      ∑ j ∈ I, v j • fourierBasis (T := T) (2*j+1) := by
    rw [circle_odd_polynomial_h4_coe, circle_odd_polynomial_l2]
    simp only [pow_zero, mul_one]
  rw [hcoe]
  simp only [circleOddPolynomialH4, map_sum, map_smul]
  rw [sum_inner, sum_inner]
  simp only [inner_sum, inner_smul_left, inner_smul_right]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have he := circle_bloch_odd_symmetric_pairing T h h₁ h₂ hh hh₁ hs hc hr α
    (2*i+1) (2*j+1) ⟨i, by ring⟩ ⟨j, by ring⟩
  unfold oddEnergyTerm oddIndexedMatrix
  rw [← he]
  ring

theorem circle_odd_polynomial_bloch_energy (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (α : ℝ) (I : Finset ℤ) (v : ℤ → ℂ) :
    (inner ℂ (circleOddPolynomialH4 T I v : CircleL2 T)
      (circleBlochOperator T h h₁ h₂ α (circleOddPolynomialH4 T I v))).re =
        (∑ i ∈ I, ∑ j ∈ I, oddEnergyTerm α v (i,j)).re := by
  rw [← circle_odd_polynomial_h4_symmetric_pairing T h h₁ h₂ hh hh₁ hs hc hr α I v]
  have hz (z : ℂ) : ((z+conj z)/2).re = z.re := by simp <;> ring
  calc
    _ = ((inner ℂ (circleOddPolynomialH4 T I v : CircleL2 T)
        (circleBlochOperator T h h₁ h₂ α (circleOddPolynomialH4 T I v))+
      conj (inner ℂ (circleOddPolynomialH4 T I v : CircleL2 T)
        (circleBlochOperator T h h₁ h₂ α (circleOddPolynomialH4 T I v))))/2).re := (hz _).symm
    _ = _ := by rw [inner_conj_symm]

theorem circle_odd_polynomial_bloch_dissipative (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2)
    (I : Finset ℤ) (v : ℤ → ℂ) :
    (inner ℂ (circleOddPolynomialH4 T I v : CircleL2 T)
      (circleBlochOperator T h h₁ h₂ α (circleOddPolynomialH4 T I v))).re ≤
        -(∑ i ∈ I, ‖v i‖^2) := by
  rw [circle_odd_polynomial_bloch_energy T h h₁ h₂ hh hh₁ hs hc hr]
  exact odd_finite_form_dissipative I v α hα hα'

end Lemniscate
