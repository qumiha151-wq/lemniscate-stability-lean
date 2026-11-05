import Lemniscate.ShortOutsideCoefficients

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

include hh hh₁ hs hc hr in
theorem circle_short_positive_outside_column (k : Fin 3) (hk : k≠0)
    (i : Fin 15) (n : ℤ) (hn : shortHeadIndex n=none) :
    circleShortSymmetricCoefficient T h h₁ h₂ (k.castLE (by decide : 3≤5))
      (circleFourierH4 T (shortHeadFrequency i)) (circleFourierH4 T (2*n))=
      (shortOutsideHColumn lemniscateFrequencySquared shortActualCoefficient k n i:ℂ) := by
  have hk5 : k.castLE (by decide : 3≤5)≠0 := by
    intro he
    apply hk
    apply Fin.ext
    exact congrArg (fun x : Fin 5 => x.val) he
  have hb (m : ℤ) (f : CircleL2 T) :
      inner ℂ (fourierBasis (T:=T) m) f=fourierCoeff f m := by
    rw [← fourierBasis_repr,HilbertBasis.repr_apply_apply]
  rw [circleShortSymmetricCoefficient,if_neg hk5]
  change (1/2:ℂ)*(inner ℂ (fourierBasis (T:=T) (shortHeadFrequency i)) _+
    inner ℂ _ (fourierBasis (T:=T) (2*n)))=_
  rw [← inner_conj_symm _ (fourierBasis (T:=T) (2*n)),hb,hb]
  change (1/2:ℂ)*((circleShortHeadCoordinates T _ ) i+conj _) = _
  rw [circle_short_transformed_head_outside T h h₁ h₂ hh hh₁ hs hc hr _ n hn,
    ← circle_short_head_single T i,
    circle_short_transformed_outside_head T h h₁ h₂ hh hh₁ hs hc hr _ _ n hn]
  simp only [Matrix.mulVec_single_one,Matrix.col_apply,shortComplexMatrix]
  simp only [shortOutsideHColumn,if_neg hk,Matrix.mulVec,dotProduct,map_sum,map_mul,
    Complex.conj_ofReal]
  push_cast
  simp only [Finset.sum_add_distrib,shortComplexMatrix]
  ring

include hh hh₁ hreal h₁real h₂real hs hc hr in
theorem circle_short_zero_outside_column (i : Fin 15) (n : ℤ)
    (hn : shortHeadIndex n=none) :
    circleShortSymmetricCoefficient T h h₁ h₂ 0
      (circleFourierH4 T (shortHeadFrequency i)) (circleFourierH4 T (2*n))=
      (shortOutsideHColumn lemniscateFrequencySquared shortActualCoefficient 0 n i:ℂ) := by
  have hu : circleShortHouseholderH4 T (circleFourierH4 T (2*n))=
      circleFourierH4 T (2*n) := by
    unfold circleShortHouseholderH4
    rw [circle_short_rotation_head,circle_short_anchor_head]
    exact circle_short_head_householder_outside T _ _ _ (short_outside_frequency_ne n hn)
  have hb (m : ℤ) (f : CircleL2 T) :
      inner ℂ (fourierBasis (T:=T) m) f=fourierCoeff f m := by
    rw [← fourierBasis_repr,HilbertBasis.repr_apply_apply]
  rw [circle_short_zero_symmetric T h h₁ h₂ hh hh₁ hreal h₁real h₂real,
    hu,← circle_short_head_single T i,circle_short_householder_head]
  rw [← inner_conj_symm _ (circleFourierH4 T (2*n):CircleL2 T)]
  change (1/2:ℂ)*(inner ℂ (circleShortHead T _:CircleL2 T) _+
    conj (inner ℂ (fourierBasis (T:=T) (2*n)) _))=_
  rw [circle_short_head_pairing,hb,
    circle_short_bloch_outside_head T h h₁ h₂ hh hh₁ hs hc hr]
  change (1/2:ℂ)*((∑ a,conj _*(circleShortHeadCoordinates T _) a)+conj _) = _
  rw [circle_short_bloch_head_outside T h h₁ h₂ hh hh₁ hs hc hr]
  have ht (a : Fin 15) : shortHouseholder shortActualCoefficient a i=
      shortHouseholder shortActualCoefficient i a :=
    congrFun (congrFun (short_householder_transpose shortActualCoefficient) i) a
  simp only [Matrix.mulVec_single_one,Matrix.col_apply,shortComplexMatrix]
  simp only [shortOutsideHColumn,↓reduceIte,map_sum,map_mul,Complex.conj_ofReal,ht]
  push_cast
  simp only [div_eq_mul_inv,mul_add,← mul_assoc,Finset.sum_add_distrib,← Finset.sum_mul]
  ring

end Coefficients
end Lemniscate
