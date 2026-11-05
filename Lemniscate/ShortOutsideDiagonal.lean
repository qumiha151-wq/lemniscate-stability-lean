import Lemniscate.ShortOutsideCoefficients

namespace Lemniscate
open Complex Matrix MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0<T)]

theorem circle_short_householder_basis_outside (n : ℤ) (hn : shortHeadIndex n=none) :
    circleShortHouseholderH4 T (circleFourierH4 T (2*n))=circleFourierH4 T (2*n) := by
  unfold circleShortHouseholderH4
  rw [circle_short_rotation_head,circle_short_anchor_head]
  exact circle_short_head_householder_outside T _ _ _ (short_outside_frequency_ne n hn)

section Coefficients
variable (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x,conj (h x)=h x) (h₁real : ∀ x,conj (h₁ x)=h₁ x)
    (h₂real : ∀ x,conj (h₂ x)=h₂ x)
    (hs : ∀ n : ℤ,fourierCoeff h (-n)=fourierCoeff h n)
    (hc : ∀ j : ℕ,fourierCoeff h (2*(j:ℤ))=(shortActualCoefficient j:ℂ))
    (hr : (2*Real.pi/T)^2=lemniscateFrequencySquared)

include hh hh₁ hs hc hr in
theorem circle_short_transformed_outside_pairing (j : Fin 5) (n m : ℤ)
    (hn : shortHeadIndex n=none) (hm : shortHeadIndex m=none) :
    inner ℂ (circleFourierH4 T (2*n):CircleL2 T)
      (circleShortTransformedCoefficient T h h₁ h₂ j (circleFourierH4 T (2*m)))=
      (shortBlochEntry lemniscateFrequencySquared shortActualCoefficient j (2*n) (2*m):ℂ) := by
  change inner ℂ (fourierBasis (T:=T) (2*n)) _=_
  rw [← HilbertBasis.repr_apply_apply,fourierBasis_repr]
  unfold circleShortTransformedCoefficient circleShortHouseholder circleShortHouseholderH4
  rw [← circle_householder_anchor_h4_coe T,circle_short_rotation_head,
    circle_short_adjoint_head,circle_short_anchor_head]
  rw [circle_short_householder_output_outside T _ _ _ _ (short_outside_frequency_ne n hn),
    circle_short_neutral_output_outside T _ _ _ _ (short_outside_frequency_ne n hn),
    circle_short_head_householder_outside T _ _ _ (short_outside_frequency_ne m hm),
    circle_short_head_neutral_inv_outside T _ _ _ (short_outside_frequency_ne m hm)]
  exact circle_short_bloch_basis_fourier T h h₁ h₂ hh hh₁ hs hc hr j n m

include hh hh₁ hreal h₁real h₂real hs hc hr in
theorem circle_short_symmetric_outside_pairing (j : Fin 5) (n m : ℤ)
    (hn : shortHeadIndex n=none) (hm : shortHeadIndex m=none) :
    circleShortSymmetricCoefficient T h h₁ h₂ j
      (circleFourierH4 T (2*n)) (circleFourierH4 T (2*m))=
      (((shortBlochEntry lemniscateFrequencySquared shortActualCoefficient j (2*n) (2*m)+
        shortBlochEntry lemniscateFrequencySquared shortActualCoefficient j (2*m) (2*n))/2:ℝ):ℂ) := by
  by_cases hj : j=0
  · subst j
    rw [circle_short_zero_symmetric T h h₁ h₂ hh hh₁ hreal h₁real h₂real,
      circle_short_householder_basis_outside T n hn,circle_short_householder_basis_outside T m hm,
      ← inner_conj_symm _ (circleFourierH4 T (2*m):CircleL2 T)]
    change (1/2:ℂ)*(inner ℂ (fourierBasis (T:=T) (2*n)) _+
      conj (inner ℂ (fourierBasis (T:=T) (2*m)) _))=_
    rw [short_circle_bloch_basis_pairing T h h₁ h₂ hh hh₁ _ _ hs hc hr,
      short_circle_bloch_basis_pairing T h h₁ h₂ hh hh₁ _ _ hs hc hr]
    simp only [Complex.conj_ofReal]
    push_cast
    ring
  · rw [circleShortSymmetricCoefficient,if_neg hj,
      ← inner_conj_symm _ (circleFourierH4 T (2*m):CircleL2 T),
      circle_short_transformed_outside_pairing T h h₁ h₂ hh hh₁ hs hc hr j n m hn hm,
      circle_short_transformed_outside_pairing T h h₁ h₂ hh hh₁ hs hc hr j m n hm hn]
    simp only [Complex.conj_ofReal]
    push_cast
    ring

include hh hh₁ hs hc hr in
theorem circle_short_high_coefficient_outside_column (j : Fin 5) (hj : j=3 ∨ j=4)
    (i : Fin 15) (n : ℤ) (hn : shortHeadIndex n=none) :
    circleShortSymmetricCoefficient T h h₁ h₂ j
      (circleFourierH4 T (shortHeadFrequency i)) (circleFourierH4 T (2*n))=0 := by
  have hne (a : Fin 15) : 2*n≠shortHeadFrequency a := short_outside_frequency_ne n hn a
  have hfwd (a : Fin 15) :
      shortBlochEntry lemniscateFrequencySquared shortActualCoefficient j
        (shortHeadFrequency a) (2*n)=0 := by
    rcases hj with rfl | rfl <;> simp [shortBlochEntry,Ne.symm (hne a)]
  have hrev (a : Fin 15) :
      shortBlochEntry lemniscateFrequencySquared shortActualCoefficient j
        (2*n) (shortHeadFrequency a)=0 := by
    rcases hj with rfl | rfl <;> simp [shortBlochEntry,hne a]
  have hj0 : j≠0 := by rcases hj with rfl | rfl <;> decide
  have hb (m : ℤ) (f : CircleL2 T) :
      inner ℂ (fourierBasis (T:=T) m) f=fourierCoeff f m := by
    rw [← fourierBasis_repr,HilbertBasis.repr_apply_apply]
  rw [circleShortSymmetricCoefficient,if_neg hj0]
  change (1/2:ℂ)*(inner ℂ (fourierBasis (T:=T) (shortHeadFrequency i)) _+
    inner ℂ _ (fourierBasis (T:=T) (2*n)))=_
  rw [← inner_conj_symm _ (fourierBasis (T:=T) (2*n)),hb,hb]
  change (1/2:ℂ)*((circleShortHeadCoordinates T _) i+conj _)=_
  rw [circle_short_transformed_head_outside T h h₁ h₂ hh hh₁ hs hc hr _ n hn,
    ← circle_short_head_single T i,
    circle_short_transformed_outside_head T h h₁ h₂ hh hh₁ hs hc hr _ _ n hn]
  simp only [hfwd,hrev,Complex.ofReal_zero,mul_zero,Finset.sum_const_zero,map_zero]
  change (1/2:ℂ)*((shortComplexMatrix _*ᵥ0) i+0)=0
  simp

end Coefficients
end Lemniscate
