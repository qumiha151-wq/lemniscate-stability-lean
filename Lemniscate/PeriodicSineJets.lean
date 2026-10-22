import Lemniscate.PeriodicCosineJets
import Lemniscate.PeriodicSineSpace

/-! Classical derivatives of the normalized positive even sine modes and the
actual fourth-order differential expression on those modes. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_deriv_sub (f f₁ g g₁ : C(AddCircle T, ℂ))
    (hf : HasCircleDeriv T f f₁) (hg : HasCircleDeriv T g g₁) :
    HasCircleDeriv T (f-g) (f₁-g₁) := by
  intro x
  exact (hf x).sub (hg x)

theorem circle_continuous_l2_sub (f g : C(AddCircle T, ℂ)) :
    circleContinuousL2 T (f-g) = circleContinuousL2 T f-circleContinuousL2 T g :=
  (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ).map_sub f g

noncomputable def circleSineJet (j k : ℕ) : C(AddCircle T, ℂ) :=
  evenSineFactor •
    ((circleFrequencyFactor T (2*((j+1:ℕ):ℤ)))^k • fourier (2*((j+1:ℕ):ℤ)) -
      (circleFrequencyFactor T (-(2*((j+1:ℕ):ℤ))))^k • fourier (-(2*((j+1:ℕ):ℤ))))

theorem circle_sine_jet_deriv (j k : ℕ) :
    HasCircleDeriv T (circleSineJet T j k) (circleSineJet T j (k+1)) :=
  circle_deriv_smul T _ _ _ (circle_deriv_sub T _ _ _ _
    (circle_fourier_derivative_power T (2*((j+1:ℕ):ℤ)) k)
    (circle_fourier_derivative_power T (-(2*((j+1:ℕ):ℤ))) k))

theorem circle_sine_jet_zero_l2 (j : ℕ) :
    circleContinuousL2 T (circleSineJet T j 0) = circleEvenSineMode T j := by
  simp only [circleSineJet, pow_zero, one_smul, circle_continuous_l2_smul,
    circle_continuous_l2_sub, circle_continuous_l2_fourier_basis, circleEvenSineMode, evenSineMode]

theorem circle_sine_inner_fourier (j : ℕ) (f : C(AddCircle T, ℂ)) :
    inner ℂ (circleEvenSineMode T j) (circleContinuousL2 T f) =
      conj evenSineFactor*(fourierCoeff f (2*((j+1:ℕ):ℤ)) -
        fourierCoeff f (-(2*((j+1:ℕ):ℤ)))) := by
  simp only [circleEvenSineMode, evenSineMode, inner_smul_left, inner_sub_left,
    ← HilbertBasis.repr_apply_apply, fourierBasis_repr, circle_continuous_l2_fourier]

noncomputable def circleSymmetricSineMode (h h₁ h₂ : C(AddCircle T, ℂ)) (j : ℕ) :
    C(AddCircle T, ℂ) :=
  circleSymmetricExpression T h h₁ h₂ (circleSineJet T j 0)
    (circleSineJet T j 1) (circleSineJet T j 2) (circleSineJet T j 4)

theorem circle_symmetric_sine_mode_eq (h h₁ h₂ : C(AddCircle T, ℂ)) (j : ℕ) :
    circleSymmetricSineMode T h h₁ h₂ j =
      evenSineFactor • (circleSymmetricMode T h h₁ h₂ (2*((j+1:ℕ):ℤ)) -
        circleSymmetricMode T h h₁ h₂ (-(2*((j+1:ℕ):ℤ)))) := by
  simp only [circleSymmetricSineMode, circleSineJet, pow_zero, pow_one, one_smul,
    circleSymmetricMode, circleSymmetricExpression]
  ext x
  simp only [ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.mul_apply, ContinuousMap.smul_apply, smul_eq_mul]
  ring

theorem circle_symmetric_sine_fourier (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂) (j : ℕ) (n : ℤ) :
    fourierCoeff (circleSymmetricSineMode T h h₁ h₂ j) n =
      evenSineFactor*(circleSymmetricFourierEntry T h n (2*((j+1:ℕ):ℤ)) -
        circleSymmetricFourierEntry T h n (-(2*((j+1:ℕ):ℤ)))) := by
  rw [circle_symmetric_sine_mode_eq]
  simp only [circle_continuous_fourier_smul, circle_continuous_fourier_sub,
    circle_symmetric_mode_fourier T h h₁ h₂ hh hh₁]

end Lemniscate
