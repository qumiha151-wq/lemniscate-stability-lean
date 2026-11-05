import Lemniscate.ShortOutsideSymmetric
import Lemniscate.ShortOutsideDiagonal
import Lemniscate.ShortCircleLinear

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
theorem circle_short_symmetric_head_outside (k : Fin 3) (v : Fin 15 → ℂ)
    (n : ℤ) (hn : shortHeadIndex n=none) :
    circleShortSymmetricCoefficient T h h₁ h₂ (k.castLE (by decide : 3≤5))
      (circleShortHead T v) (circleFourierH4 T (2*n))=
      ∑ i,conj (v i)*(shortOutsideHColumn lemniscateFrequencySquared
        shortActualCoefficient k n i:ℂ) := by
  have hb (i : Fin 15) : circleShortSymmetricCoefficient T h h₁ h₂
      (k.castLE (by decide : 3≤5)) (circleFourierH4 T (shortHeadFrequency i))
        (circleFourierH4 T (2*n))=
        (shortOutsideHColumn lemniscateFrequencySquared shortActualCoefficient k n i:ℂ) := by
    by_cases hk : k=0
    · subst k
      exact circle_short_zero_outside_column T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr i n hn
    · exact circle_short_positive_outside_column T h h₁ h₂ hh hh₁ hs hc hr k hk i n hn
  change circleShortSymmetricCoefficient T h h₁ h₂ _
    (∑ i : Fin 15,v i • circleFourierH4 T (shortHeadFrequency i)) _=_
  rw [circle_short_symmetric_sum_left]
  simp only [circle_short_symmetric_smul_left,hb]

include hh hh₁ hs hc hr in
theorem circle_short_high_coefficient_head_outside (j : Fin 5) (hj : j=3 ∨ j=4)
    (v : Fin 15 → ℂ) (n : ℤ) (hn : shortHeadIndex n=none) :
    circleShortSymmetricCoefficient T h h₁ h₂ j
      (circleShortHead T v) (circleFourierH4 T (2*n))=0 := by
  change circleShortSymmetricCoefficient T h h₁ h₂ _
    (∑ i : Fin 15,v i • circleFourierH4 T (shortHeadFrequency i)) _=_
  rw [circle_short_symmetric_sum_left]
  simp only [circle_short_symmetric_smul_left,
    circle_short_high_coefficient_outside_column T h h₁ h₂ hh hh₁ hs hc hr j hj _ n hn,
    mul_zero,Finset.sum_const_zero]

include hh hh₁ hreal h₁real h₂real hs hc hr in
theorem circle_short_reduced_outside_column (k : Fin 5) (i : Fin 15)
    (n : ℤ) (hn : shortHeadIndex n=none) :
    circleReducedShiftedCoefficient T (circleShortSymmetricCoefficient T h h₁ h₂) k
      (circleFourierH4 T (shortHeadFrequency i)) (circleFourierH4 T (2*n))=
      ![(shortOutsideGColumn lemniscateFrequencySquared shortActualCoefficient 0 n i:ℂ),
        (shortOutsideGColumn lemniscateFrequencySquared shortActualCoefficient 1 n i:ℂ),
        (shortOutsideGColumn lemniscateFrequencySquared shortActualCoefficient 2 n i:ℂ),0,0] k := by
  have h0 (v : Fin 15 → ℂ) : circleShortSymmetricCoefficient T h h₁ h₂ 0
      (circleShortHead T v) (circleFourierH4 T (2*n))=
      ∑ a,conj (v a)*(shortOutsideHColumn lemniscateFrequencySquared shortActualCoefficient 0 n a:ℂ) :=
    circle_short_symmetric_head_outside T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr 0 v n hn
  have h1 (v : Fin 15 → ℂ) : circleShortSymmetricCoefficient T h h₁ h₂ 1
      (circleShortHead T v) (circleFourierH4 T (2*n))=
      ∑ a,conj (v a)*(shortOutsideHColumn lemniscateFrequencySquared shortActualCoefficient 1 n a:ℂ) :=
    circle_short_symmetric_head_outside T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr 1 v n hn
  have h2 (v : Fin 15 → ℂ) : circleShortSymmetricCoefficient T h h₁ h₂ 2
      (circleShortHead T v) (circleFourierH4 T (2*n))=
      ∑ a,conj (v a)*(shortOutsideHColumn lemniscateFrequencySquared shortActualCoefficient 2 n a:ℂ) :=
    circle_short_symmetric_head_outside T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr 2 v n hn
  have h3 (v) := circle_short_high_coefficient_head_outside T h h₁ h₂ hh hh₁ hs hc hr 3
    (Or.inl rfl) v n hn
  have hp (a : Fin 15) : shortStableProjection a i=shortStableProjection i a :=
    congrFun (congrFun short_stable_projection_transpose i) a
  have hp0 (a : Fin 15) : shortCenterProjection a i=shortCenterProjection i a :=
    congrFun (congrFun short_center_projection_transpose i) a
  rw [← circle_short_head_single T i]
  fin_cases k <;>
    simp only [circleReducedShiftedCoefficient,Matrix.cons_val_zero',Matrix.cons_val_succ',
      circle_short_fixed_projection_outside T (2*n) (short_outside_frequency_ne n hn),sub_zero]
  all_goals
    simp only [circle_short_stable_projection_head]
    simp only [circle_short_fixed_projection_head,circle_short_symmetric_zero_right,
      Submodule.coe_zero,inner_zero_right,h0,h1,h2,h3,
      circle_short_head_basis_outside T _ (2*n) (short_outside_frequency_ne n hn),
      add_zero,mul_zero]
  all_goals
    simp only [Matrix.mulVec_single_one,Matrix.col_apply,shortComplexMatrix,
      Complex.conj_ofReal,hp,hp0]
    norm_num [shortOutsideGColumn,Matrix.mulVec,dotProduct] <;> rfl

include hh hh₁ hreal h₁real h₂real hs hc hr in
theorem circle_short_bernstein_outside_column (j : Fin 5) (i : Fin 15)
    (n : ℤ) (hn : shortHeadIndex n=none) :
    circleShortBernsteinPairing T h h₁ h₂ j
      (circleFourierH4 T (shortHeadFrequency i)) (circleFourierH4 T (2*n))=
      (shortOutsideBernsteinColumn lemniscateFrequencySquared shortActualCoefficient j n i:ℂ) := by
  simp only [circleShortBernsteinPairing,circleShiftedBernsteinPairing,
    circle_short_reduced_outside_column T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr _ i n hn]
  norm_num [shortOutsideBernsteinColumn,Fin.sum_univ_succ]

end Coefficients
end Lemniscate
