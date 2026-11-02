import Lemniscate.PeriodicShiftedWeakCalculus
import Lemniscate.PeriodicProfileBounds

/-! The energy identity and Garding estimate are unchanged by an imaginary
constant shift of the derivative. Only two shifted derivatives enter the form. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_shifted_linear_energy (z : ℂ) (hz : conj z = -z)
    (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) (f f₁ f₂ f₃ f₄ : CircleL2 T)
    (hf : HasWeakCircleShiftedDeriv T z f f₁)
    (hf₁ : HasWeakCircleShiftedDeriv T z f₁ f₂)
    (hf₂ : HasWeakCircleShiftedDeriv T z f₂ f₃)
    (hf₃ : HasWeakCircleShiftedDeriv T z f₃ f₄) :
    (inner ℂ f (circleLinearL2Expression T h h₁ h₂ f f₁ f₂ f₄)).re =
      circleH2Energy T h h₂ f f₁ f₂ := by
  have hfourth := circle_shifted_fourth_pairing T z hz f f₁ f₂ f₃ f₄ hf hf₁ hf₂ hf₃
  have hd := circle_shifted_integration_by_parts T z hz f f₁ (circleMultiplyL2 T h f₁)
    (circleMultiplyL2 T h f₂+circleMultiplyL2 T h₁ f₁) hf
    (circle_shifted_multiply_weak_deriv T z h h₁ hh hreal h₁real f₁ f₂ hf₁)
  have hdiv : inner ℂ f (circleMultiplyL2 T h₁ f₁+circleMultiplyL2 T h f₂) =
      -inner ℂ f₁ (circleMultiplyL2 T h f₁) := by
    rw [add_comm]
    exact neg_eq_iff_eq_neg.mp hd.symm
  have hs : (inner ℂ f (circleSymmetricL2Expression T h h₁ h₂ f f₁ f₂ f₄)).re =
      circleH2Energy T h h₂ f f₁ f₂ := by
    unfold circleSymmetricL2Expression circleH2Energy
    apply congrArg Complex.re
    simp only [inner_add_right,inner_sub_right,inner_smul_right]
    simp only [inner_add_right] at hdiv
    rw [hfourth,hdiv]
    ring
  have hk := circle_shifted_skew_energy T z hz h₁ h₂ hh₁ h₁real h₂real f f₁ hf
  unfold circleLinearL2Expression
  rw [inner_add_right,inner_smul_right,Complex.add_re,Complex.mul_re]
  norm_num
  rw [hk,hs]
  ring

theorem paper_shifted_energy_garding (z : ℂ) (hz : conj z = -z)
    (q : C(AddCircle T, ℂ)) (hqreal : ∀ x, conj (q x) = q x) (hqnorm : ‖q‖ ≤ 1)
    (f f₁ f₂ : CircleL2 T)
    (hf : HasWeakCircleShiftedDeriv T z f f₁)
    (hf₁ : HasWeakCircleShiftedDeriv T z f₁ f₂) :
    paperH2Energy T q f f₁ f₂ ≤ -2*‖f₂‖^2+(1719/8:ℝ)*‖f‖^2 := by
  have hm : ‖circleMultiplyL2 T q f₁‖ ≤ ‖f₁‖ := by
    calc
      _ ≤ ‖q‖*‖f₁‖ := circle_multiply_l2_norm_le T q f₁
      _ ≤ 1*‖f₁‖ := mul_le_mul_of_nonneg_right hqnorm (norm_nonneg _)
      _ = _ := one_mul _
  have hm2 := pow_le_pow_left₀ (norm_nonneg _) hm 2
  have hd := circle_shifted_derivative_norm_sq_product T z hz f f₁ f₂ hf hf₁
  apply garding_interpolation
  rw [paper_h2_energy_squared_norms T q hqreal]
  nlinarith [sq_nonneg ‖circleMultiplyL2 T (q^2) f‖]

end Lemniscate
