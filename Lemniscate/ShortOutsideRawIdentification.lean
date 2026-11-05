import Lemniscate.ShortOutsideDiagonal
import Lemniscate.ShortCircleLinear

namespace Lemniscate
open Complex Matrix MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0<T)]

theorem circle_short_even_basis_inner (n m : ℤ) :
    inner ℂ (circleFourierH4 T (2*n):CircleL2 T) (circleFourierH4 T (2*m):CircleL2 T)=
      if n=m then 1 else 0 := by
  have hb := orthonormal_iff_ite.mp (fourierBasis (T:=T)).orthonormal
  change inner ℂ (fourierBasis (T:=T) (2*n)) (fourierBasis (T:=T) (2*m))=_
  rw [hb]
  simp only [show (2*n=2*m)↔n=m by omega]

section Coefficients
variable (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x,conj (h x)=h x) (h₁real : ∀ x,conj (h₁ x)=h₁ x)
    (h₂real : ∀ x,conj (h₂ x)=h₂ x)
    (hs : ∀ n : ℤ,fourierCoeff h (-n)=fourierCoeff h n)
    (hc : ∀ j : ℕ,fourierCoeff h (2*(j:ℤ))=(shortActualCoefficient j:ℂ))
    (hr : (2*Real.pi/T)^2=lemniscateFrequencySquared)

include hh hh₁ hreal h₁real h₂real hs hc hr in
theorem circle_short_reduced_outside_pairing (k : Fin 5) (n m : ℤ)
    (hn : shortHeadIndex n=none) (hm : shortHeadIndex m=none) :
    circleReducedShiftedCoefficient T (circleShortSymmetricCoefficient T h h₁ h₂) k
      (circleFourierH4 T (2*n)) (circleFourierH4 T (2*m))=
      (((shortBlochEntry lemniscateFrequencySquared shortActualCoefficient k (2*n) (2*m)+
        shortBlochEntry lemniscateFrequencySquared shortActualCoefficient k (2*m) (2*n))/2:ℝ):ℂ)+
        if k=0 ∧ n=m then (1/2:ℂ) else 0 := by
  have hr4 : (2*Real.pi/T)^4=lemniscateFrequencySquared^2 := by
    rw [show (2*Real.pi/T)^4=((2*Real.pi/T)^2)^2 by ring,hr]
  fin_cases k <;>
    simp only [circleReducedShiftedCoefficient,Matrix.cons_val_zero',Matrix.cons_val_succ',
      circle_short_fixed_projection_outside T (2*n) (short_outside_frequency_ne n hn),
      circle_short_fixed_projection_outside T (2*m) (short_outside_frequency_ne m hm),
      sub_zero,circle_short_symmetric_zero_left,circle_short_symmetric_zero_right,
      Submodule.coe_zero,inner_zero_left,inner_zero_right,mul_zero,add_zero,zero_add,
      circle_short_symmetric_outside_pairing T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr _ n m hn hm,
      circle_short_even_basis_inner,hr4]
  all_goals
    by_cases heq : n=m <;>
      norm_num [heq,shortBlochEntry,show (2*n=2*m)↔n=m by omega,
        show (2*m=2*n)↔n=m by omega] <;> push_cast <;> ring

include hh hh₁ hreal h₁real h₂real hs hc hr in
theorem circle_short_bernstein_outside_pairing (j : Fin 5) (n m : ℤ)
    (hn : shortHeadIndex n=none) (hm : shortHeadIndex m=none) :
    circleShortBernsteinPairing T h h₁ h₂ j
      (circleFourierH4 T (2*n)) (circleFourierH4 T (2*m))=
      (shortRawBernsteinEntry lemniscateFrequencySquared shortActualCoefficient j n m:ℂ) := by
  simp only [circleShortBernsteinPairing,circleShiftedBernsteinPairing,
    circle_short_reduced_outside_pairing T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc hr _ n m hn hm,
    mul_add,Finset.sum_add_distrib,shortRawBernsteinEntry]
  push_cast
  by_cases heq : n=m
  · simp only [heq,and_true,ite_mul,mul_ite,mul_zero,Finset.sum_ite_eq,
      Finset.mem_univ,if_true]
    norm_num [shortBernsteinWeight]
    ring
  · simp only [heq,and_false,if_false,mul_zero,Finset.sum_const_zero,
      Complex.ofReal_zero,add_zero,zero_add]

end Coefficients
end Lemniscate
