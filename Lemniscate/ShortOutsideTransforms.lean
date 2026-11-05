import Lemniscate.ShortHeadProjection
import Lemniscate.ShortSchurKernel

namespace Lemniscate
open Complex Matrix MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

theorem short_outside_frequency_ne (n : ℤ) (hn : shortHeadIndex n=none)
    (i : Fin 15) : 2*n≠shortHeadFrequency i := by
  intro hi
  have hb : -7≤n ∧ n≤7 := by
    have := i.isLt
    dsimp only [shortHeadFrequency] at hi
    omega
  simp [shortHeadIndex,hb] at hn

variable (T : ℝ) [Fact (0<T)]

theorem circle_short_head_fourier_outside (v : Fin 15 → ℂ) (n : ℤ)
    (hn : ∀ i : Fin 15,n≠shortHeadFrequency i) :
    fourierCoeff (circleShortHead T v:CircleL2 T) n=0 := by
  simp only [circle_short_head_fourier,if_neg (hn _),mul_zero,Finset.sum_const_zero]

theorem circle_short_head_basis_outside (v : Fin 15 → ℂ) (n : ℤ)
    (hn : ∀ i : Fin 15,n≠shortHeadFrequency i) :
    inner ℂ (circleShortHead T v:CircleL2 T) (circleFourierH4 T n:CircleL2 T)=0 := by
  have hz := circle_short_head_fourier_outside T v n hn
  rw [← fourierBasis_repr,HilbertBasis.repr_apply_apply] at hz
  exact inner_eq_zero_symm.mpr hz

theorem circle_short_head_householder_outside (e a : Fin 15 → ℂ) (n : ℤ)
    (hn : ∀ i : Fin 15,n≠shortHeadFrequency i) :
    neutralHouseholderDomain (circleShortHead T e) (circleShortHead T a)
      (circleFourierH4 T n)=circleFourierH4 T n := by
  simp only [neutralHouseholderDomain,inner_add_left,
    circle_short_head_basis_outside T _ n hn,add_zero,mul_zero,zero_smul,sub_zero]

theorem circle_short_head_neutral_inv_outside (e p : Fin 15 → ℂ) (n : ℤ)
    (hn : ∀ i : Fin 15,n≠shortHeadFrequency i) :
    neutralTransformInvDomain (circleShortHead T e) (circleShortHead T p:CircleL2 T)
      (circleFourierH4 T n)=circleFourierH4 T n := by
  simp only [neutralTransformInvDomain,inner_sub_left,
    circle_short_head_basis_outside T _ n hn,sub_self,zero_smul,sub_zero]

theorem circle_short_householder_output_outside (e a : Fin 15 → ℂ) (f : CircleL2 T)
    (n : ℤ) (hn : ∀ i : Fin 15,n≠shortHeadFrequency i) :
    fourierCoeff (neutralHouseholder (circleShortHead T e:CircleL2 T)
      (circleShortHead T a:CircleL2 T) f) n=fourierCoeff f n := by
  simp only [neutral_householder_apply,circle_fourierCoeff_sub,circle_fourierCoeff_smul,
    circle_fourierCoeff_add,circle_short_head_fourier_outside T _ n hn,
    add_zero,mul_zero,sub_zero]

theorem circle_short_neutral_output_outside (e p : Fin 15 → ℂ) (f : CircleL2 T)
    (n : ℤ) (hn : ∀ i : Fin 15,n≠shortHeadFrequency i) :
    fourierCoeff (neutralTransform (circleShortHead T e)
      (circleShortHead T p:CircleL2 T) f) n=fourierCoeff f n := by
  simp only [neutral_transform_apply,circle_fourierCoeff_add,circle_fourierCoeff_smul,
    circle_short_head_fourier_outside T _ n hn,mul_zero,add_zero]

theorem circle_short_fixed_projection_outside (n : ℤ)
    (hn : ∀ i : Fin 15,n≠shortHeadFrequency i) :
    circleFixedProjectionH4 T (circleFourierH4 T n)=0 := by
  rw [circleFixedProjectionH4,← circle_householder_anchor_h4_coe T,circle_short_anchor_head,
    circle_short_head_basis_outside T _ n hn,zero_smul]

end Lemniscate
