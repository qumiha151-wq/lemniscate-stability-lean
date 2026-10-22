import Lemniscate.PeriodicSinePolynomials
import Lemniscate.SineBlockFormLimit
import Lemniscate.PeriodicIntegrationByParts

/-! The actual differential energy of every finite sine polynomial agrees
with the certified first-mode/tail coefficient block, including both cross terms. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_sine_polynomial_energy_eq_matrix (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (I : Finset ℕ) (u : ℂ) (v : ℕ → ℂ) :
    inner ℂ (circleContinuousL2 T (circleSinePolynomial T I u v 0))
      (circleContinuousL2 T (circleSymmetricSinePolynomial T h h₁ h₂ I u v)) =
        sineFiniteBlockPairing I u v := by
  let P : ℕ → CircleL2 T := circleEvenSineMode T
  let Q : ℕ → CircleL2 T := fun j => circleContinuousL2 T (circleSymmetricSineMode T h h₁ h₂ j)
  have hm (j k : ℕ) : inner ℂ (P j) (Q k) =
      (sineMatrixEntry thetaParameter nome (j+1) (k+1):ℂ) :=
    circle_sine_matrix_eq_coefficients T h h₁ h₂ thetaParameter nome hh hh₁ hs hc hr j k
  have h00 : inner ℂ (u • P 0) (u • Q 0) =
      conj u*(sineMatrixEntry thetaParameter nome 1 1:ℂ)*u := by
    simp only [inner_smul_left, inner_smul_right, hm, Nat.zero_add]
    ring
  have h01 : inner ℂ (u • P 0) (∑ j ∈ I, v j • Q (j+1)) =
      ∑ j ∈ I, conj u*(sineMatrixEntry thetaParameter nome 1 (j+2):ℂ)*v j := by
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [inner_smul_left, inner_smul_right, hm, Nat.zero_add,
      Nat.add_assoc, Nat.reduceAdd]
    ring
  have h10 : inner ℂ (∑ j ∈ I, v j • P (j+1)) (u • Q 0) =
      ∑ j ∈ I, conj (v j)*(sineMatrixEntry thetaParameter nome (j+2) 1:ℂ)*u := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [inner_smul_left, inner_smul_right, hm, Nat.zero_add,
      Nat.add_assoc, Nat.reduceAdd]
    ring
  have h11 : inner ℂ (∑ j ∈ I, v j • P (j+1)) (∑ j ∈ I, v j • Q (j+1)) =
      ∑ i ∈ I, ∑ j ∈ I, sineTailEnergyTerm v (i,j) := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [inner_smul_left, inner_smul_right, hm, sineTailEnergyTerm,
      Nat.add_assoc, Nat.reduceAdd]
    ring
  rw [circle_sine_polynomial_l2, circle_symmetric_sine_polynomial_sum,
    circle_continuous_l2_add, circle_continuous_l2_smul, circle_continuous_l2_sum]
  simp only [circle_continuous_l2_smul]
  change inner ℂ (u • P 0 + ∑ j ∈ I, v j • P (j+1))
    (u • Q 0 + ∑ j ∈ I, v j • Q (j+1)) = _
  rw [inner_add_left, inner_add_right, inner_add_right, h00, h01, h10, h11]
  unfold sineFiniteBlockPairing
  ring

theorem circle_sine_polynomial_h2_energy_eq (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (I : Finset ℕ) (u : ℂ) (v : ℕ → ℂ) :
    circleH2Energy T h h₂ (circleContinuousL2 T (circleSinePolynomial T I u v 0))
      (circleContinuousL2 T (circleSinePolynomial T I u v 1))
      (circleContinuousL2 T (circleSinePolynomial T I u v 2)) =
      (inner ℂ (circleContinuousL2 T (circleSinePolynomial T I u v 0))
        (circleContinuousL2 T (circleSymmetricSinePolynomial T h h₁ h₂ I u v))).re := by
  exact (circle_classical_energy_eq T h h₁ h₂
    (circleSinePolynomial T I u v 0) (circleSinePolynomial T I u v 1)
    (circleSinePolynomial T I u v 2) (circleSinePolynomial T I u v 3)
    (circleSinePolynomial T I u v 4) hh
    (circle_sine_polynomial_deriv T I u v 0) (circle_sine_polynomial_deriv T I u v 1)
    (circle_sine_polynomial_deriv T I u v 2) (circle_sine_polynomial_deriv T I u v 3)).symm

theorem circle_sine_polynomial_h2_energy_eq_coefficients (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (I : Finset ℕ) (u : ℂ) (v : ℕ → ℂ) :
    circleH2Energy T h h₂ (circleContinuousL2 T (circleSinePolynomial T I u v 0))
      (circleContinuousL2 T (circleSinePolynomial T I u v 1))
      (circleContinuousL2 T (circleSinePolynomial T I u v 2)) =
        (sineFiniteBlockPairing I u v).re := by
  rw [circle_sine_polynomial_h2_energy_eq T h h₁ h₂ hh,
    circle_sine_polynomial_energy_eq_matrix T h h₁ h₂ hh hh₁ hs hc hr]

end Lemniscate
