import Lemniscate.PeriodicSymmetricExpression

/-! Classical derivatives of all orders of normalized cosine modes, their
actual L2 pairing, and the action of the fourth-order expression on those modes. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_deriv_add (f f₁ g g₁ : C(AddCircle T, ℂ))
    (hf : HasCircleDeriv T f f₁) (hg : HasCircleDeriv T g g₁) :
    HasCircleDeriv T (f+g) (f₁+g₁) := by
  intro x
  exact (hf x).add (hg x)

theorem circle_deriv_smul (c : ℂ) (f f₁ : C(AddCircle T, ℂ))
    (hf : HasCircleDeriv T f f₁) : HasCircleDeriv T (c • f) (c • f₁) := by
  intro x
  exact (hf x).const_mul c

noncomputable def circleCosineJet (j k : ℕ) : C(AddCircle T, ℂ) :=
  if j = 0 then (circleFrequencyFactor T 0)^k • fourier 0
  else evenCosineFactor •
    ((circleFrequencyFactor T (2*(j:ℤ)))^k • fourier (2*(j:ℤ)) +
      (circleFrequencyFactor T (-(2*(j:ℤ))))^k • fourier (-(2*(j:ℤ))))

theorem circle_cosine_jet_deriv (j k : ℕ) :
    HasCircleDeriv T (circleCosineJet T j k) (circleCosineJet T j (k+1)) := by
  by_cases hj : j = 0
  · simp only [circleCosineJet, if_pos hj]
    exact circle_fourier_derivative_power T 0 k
  · simp only [circleCosineJet, if_neg hj]
    exact circle_deriv_smul T _ _ _ (circle_deriv_add T _ _ _ _
      (circle_fourier_derivative_power T (2*(j:ℤ)) k)
      (circle_fourier_derivative_power T (-(2*(j:ℤ))) k))

theorem circle_continuous_l2_add (f g : C(AddCircle T, ℂ)) :
    circleContinuousL2 T (f+g) = circleContinuousL2 T f + circleContinuousL2 T g :=
  (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ).map_add f g

theorem circle_cosine_jet_zero_l2 (j : ℕ) :
    circleContinuousL2 T (circleCosineJet T j 0) = circleEvenCosineMode T j := by
  by_cases hj : j = 0
  · subst j
    simp only [circleCosineJet, ite_true, pow_zero, one_smul,
      circle_continuous_l2_fourier_basis, circleEvenCosineMode, evenCosineMode]
  · simp only [circleCosineJet, if_neg hj, pow_zero, one_smul,
      circle_continuous_l2_smul, circle_continuous_l2_add,
      circle_continuous_l2_fourier_basis, circleEvenCosineMode, evenCosineMode]

theorem circle_cosine_inner_fourier (j : ℕ) (f : C(AddCircle T, ℂ)) :
    inner ℂ (circleEvenCosineMode T j) (circleContinuousL2 T f) =
      if j = 0 then fourierCoeff f 0 else
        evenCosineFactor * (fourierCoeff f (2*(j:ℤ)) + fourierCoeff f (-(2*(j:ℤ)))) := by
  by_cases hj : j = 0
  · subst j
    simp only [circleEvenCosineMode, evenCosineMode, ite_true,
      ← HilbertBasis.repr_apply_apply, fourierBasis_repr, circle_continuous_l2_fourier]
  · simp only [circleEvenCosineMode, evenCosineMode, if_neg hj,
      inner_smul_left, inner_add_left, evenCosineFactor_conj,
      ← HilbertBasis.repr_apply_apply, fourierBasis_repr, circle_continuous_l2_fourier]

noncomputable def circleSymmetricCosineMode (h h₁ h₂ : C(AddCircle T, ℂ)) (j : ℕ) :
    C(AddCircle T, ℂ) :=
  circleSymmetricExpression T h h₁ h₂ (circleCosineJet T j 0)
    (circleCosineJet T j 1) (circleCosineJet T j 2) (circleCosineJet T j 4)

theorem circle_symmetric_cosine_mode_eq (h h₁ h₂ : C(AddCircle T, ℂ)) (j : ℕ) :
    circleSymmetricCosineMode T h h₁ h₂ j =
      if j = 0 then circleSymmetricMode T h h₁ h₂ 0
      else evenCosineFactor • (circleSymmetricMode T h h₁ h₂ (2*(j:ℤ)) +
        circleSymmetricMode T h h₁ h₂ (-(2*(j:ℤ)))) := by
  by_cases hj : j = 0
  · simp only [circleSymmetricCosineMode, circleCosineJet, if_pos hj,
      pow_zero, pow_one, one_smul, circleSymmetricMode]
  · simp only [circleSymmetricCosineMode, circleCosineJet, if_neg hj,
      pow_zero, pow_one, one_smul, circleSymmetricMode, circleSymmetricExpression]
    ext x
    simp only [ContinuousMap.add_apply, ContinuousMap.sub_apply,
      ContinuousMap.mul_apply, ContinuousMap.smul_apply, smul_eq_mul]
    ring

theorem circle_symmetric_cosine_fourier (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂) (j : ℕ) (n : ℤ) :
    fourierCoeff (circleSymmetricCosineMode T h h₁ h₂ j) n =
      if j = 0 then circleSymmetricFourierEntry T h n 0
      else evenCosineFactor * (circleSymmetricFourierEntry T h n (2*(j:ℤ)) +
        circleSymmetricFourierEntry T h n (-(2*(j:ℤ)))) := by
  rw [circle_symmetric_cosine_mode_eq]
  by_cases hj : j = 0
  · simp only [if_pos hj, circle_symmetric_mode_fourier T h h₁ h₂ hh hh₁]
  · simp only [if_neg hj, circle_continuous_fourier_smul,
      circle_continuous_fourier_add, circle_symmetric_mode_fourier T h h₁ h₂ hh hh₁]

end Lemniscate
