import Lemniscate.ShortHeadSymmetric

namespace Lemniscate
open Complex Matrix MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0<T)]

section Coefficients
variable (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x,conj (h x)=h x) (h₁real : ∀ x,conj (h₁ x)=h₁ x)
    (h₂real : ∀ x,conj (h₂ x)=h₂ x)
    (hs : ∀ n : ℤ,fourierCoeff h (-n)=fourierCoeff h n)
    (hc : ∀ j : ℕ,fourierCoeff h (2*(j:ℤ))=(shortActualCoefficient j:ℂ))
    (hr : (2*Real.pi/T)^2=lemniscateFrequencySquared)

include hh hh₁ hreal h₁real h₂real hs hc hr in
theorem circle_short_symmetric_head_pairing (j : Fin 5) (hj4 : j≠4)
    (v w : Fin 15 → ℂ) :
    circleShortSymmetricCoefficient T h h₁ h₂ j (circleShortHead T v) (circleShortHead T w)=
      shortHeadPair v (shortComplexMatrix
        (shortTransformedCoefficient lemniscateFrequencySquared shortActualCoefficient j)*ᵥw) := by
  by_cases hj : j=0
  · subst j
    rw [circle_short_zero_symmetric T h h₁ h₂ hh hh₁ hreal h₁real h₂real,
      circle_short_householder_head,circle_short_householder_head]
    rw [← inner_conj_symm
      (circleBlochCoefficient T h h₁ h₂ 0 (circleShortHead T
        (shortComplexMatrix (shortHouseholder shortActualCoefficient)*ᵥv)))
      (circleShortHead T
        (shortComplexMatrix (shortHouseholder shortActualCoefficient)*ᵥw):CircleL2 T)]
    rw [circle_short_head_operator_pairing,circle_short_head_operator_pairing,
      circle_short_bloch_head_matrix T h h₁ h₂ hh hh₁ _ _ hs hc hr]
    rw [← short_head_pair_symmetric,short_head_pair_mulVec_left,
      short_complex_matrix_conjTranspose,short_householder_transpose]
    simp only [shortTransformedCoefficient, ↓reduceIte,short_complex_matrix_mul,
      Matrix.mulVec_mulVec,mul_assoc]
  · rw [circleShortSymmetricCoefficient,if_neg hj]
    rw [← inner_conj_symm
      (circleShortTransformedCoefficient T h h₁ h₂ j (circleShortHead T v))
      (circleShortHead T w:CircleL2 T)]
    rw [circle_short_transformed_head_pairing T h h₁ h₂ hh hh₁ hs hc hr,
      circle_short_transformed_head_pairing T h h₁ h₂ hh hh₁ hs hc hr,
      ← short_head_pair_symmetric]
    simp only [shortTransformedCoefficient,if_neg hj,if_neg hj4]

end Coefficients
end Lemniscate
