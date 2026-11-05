import Lemniscate.ShortHeadProjection

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
theorem circle_short_reduced_head_pairing (k : Fin 5) (v w : Fin 15 → ℂ) :
    circleReducedShiftedCoefficient T (circleShortSymmetricCoefficient T h h₁ h₂)
      k (circleShortHead T v) (circleShortHead T w)=
    shortHeadPair v (shortComplexMatrix
      (shortGHeadCoefficient lemniscateFrequencySquared shortActualCoefficient k)*ᵥw) := by
  have h0 := circle_short_symmetric_head_pairing T h h₁ h₂ hh hh₁ hreal h₁real h₂real
    hs hc hr 0 (by decide)
  have h1 := circle_short_symmetric_head_pairing T h h₁ h₂ hh hh₁ hreal h₁real h₂real
    hs hc hr 1 (by decide)
  have h2 := circle_short_symmetric_head_pairing T h h₁ h₂ hh hh₁ hreal h₁real h₂real
    hs hc hr 2 (by decide)
  have h3 := circle_short_symmetric_head_pairing T h h₁ h₂ hh hh₁ hreal h₁real h₂real
    hs hc hr 3 (by decide)
  have hr4 : (2*Real.pi/T)^4=lemniscateFrequencySquared^2 := by
    rw [show (2*Real.pi/T)^4=((2*Real.pi/T)^2)^2 by ring,hr]
  have hi (x y : Fin 15 → ℂ) :
      inner ℂ (circleShortHead T x:CircleL2 T) (circleShortHead T y:CircleL2 T)=
        shortHeadPair x y := circle_short_head_inner T x y
  fin_cases k <;>
    simp only [circleReducedShiftedCoefficient,shortGHeadCoefficient,
      Matrix.cons_val_zero',Matrix.cons_val_succ',hr4]
  all_goals
    simp only [circle_short_stable_projection_head]
    simp only [circle_short_fixed_projection_head,h0,h1,h2,h3,hi]
    simp only [short_complex_matrix_add,short_complex_matrix_mul,short_complex_matrix_smul,
      short_complex_matrix_one,add_mulVec,smul_mulVec,one_mulVec,
      short_head_pair_add_right,short_head_pair_smul_right,Matrix.mulVec_mulVec]
    simp only [short_head_pair_mulVec_left,short_complex_matrix_conjTranspose,
      short_center_projection_transpose,short_stable_projection_transpose,
      Matrix.mulVec_mulVec,mul_assoc,short_center_complex_sq,short_stable_complex_sq] <;>
      push_cast <;> ring

include hh hh₁ hreal h₁real h₂real hs hc hr in
theorem circle_short_bernstein_head_pairing (j : Fin 5) (v w : Fin 15 → ℂ) :
    circleShortBernsteinPairing T h h₁ h₂ j (circleShortHead T v) (circleShortHead T w)=
    shortHeadPair v (shortComplexMatrix
      (shortBernsteinHead lemniscateFrequencySquared shortActualCoefficient j)*ᵥw) := by
  have hsum (x : Fin 5 → Fin 15 → ℂ) : shortHeadPair v (∑ k,x k)=
      ∑ k,shortHeadPair v (x k) := by
    simp only [shortHeadPair,Finset.sum_apply,Finset.mul_sum]
    rw [Finset.sum_comm]
  have hcast (M : Fin 5 → Matrix (Fin 15) (Fin 15) ℝ) :
      shortComplexMatrix (∑ k,M k)=∑ k,shortComplexMatrix (M k) := by
    ext i l
    simp only [shortComplexMatrix,Matrix.sum_apply,Complex.ofReal_sum]
  simp only [circleShortBernsteinPairing,circleShiftedBernsteinPairing,
    circle_short_reduced_head_pairing T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr,
    shortBernsteinHead,hcast,Matrix.sum_mulVec,short_complex_matrix_smul,
    Matrix.smul_mulVec,hsum,short_head_pair_smul_right,Complex.ofReal_ratCast]

end Coefficients
end Lemniscate
