import Lemniscate.PeriodicWeakCalculus
import Lemniscate.PeriodicReflectionSplit

/-! Weak calculus for D+z on the periodic L2 space. Imaginary shifts retain
integration by parts and the same interpolation estimate. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

def HasWeakCircleShiftedDeriv (z : ℂ) (f f₁ : CircleL2 T) : Prop :=
  HasWeakCircleDeriv T f (f₁-z • f)

theorem circle_shifted_deriv_of_weak (z : ℂ) (f f₁ : CircleL2 T)
    (hf : HasWeakCircleDeriv T f f₁) :
    HasWeakCircleShiftedDeriv T z f (f₁+z • f) := by
  simpa only [HasWeakCircleShiftedDeriv,add_sub_cancel_right] using hf

theorem circle_shifted_deriv_fourier (z : ℂ) (f f₁ : CircleL2 T)
    (hf : HasWeakCircleShiftedDeriv T z f f₁) (n : ℤ) :
    fourierCoeff f₁ n = (circleFrequencyFactor T n+z)*fourierCoeff f n := by
  have h := fourier_of_weak_circle_deriv T f (f₁-z • f) hf n
  rw [circle_fourierCoeff_sub,circle_fourierCoeff_smul] at h
  linear_combination h

theorem circle_shifted_integration_by_parts (z : ℂ) (hz : conj z = -z)
    (f f₁ g g₁ : CircleL2 T)
    (hf : HasWeakCircleShiftedDeriv T z f f₁)
    (hg : HasWeakCircleShiftedDeriv T z g g₁) :
    inner ℂ f₁ g = -inner ℂ f g₁ := by
  have h := circle_weak_integration_by_parts T f (f₁-z • f) g (g₁-z • g) hf hg
  simp only [inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,hz] at h
  linear_combination h

theorem circle_shifted_multiply_weak_deriv (z : ℂ) (h h₁ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (f f₁ : CircleL2 T) (hf : HasWeakCircleShiftedDeriv T z f f₁) :
    HasWeakCircleShiftedDeriv T z (circleMultiplyL2 T h f)
      (circleMultiplyL2 T h f₁+circleMultiplyL2 T h₁ f) := by
  have hprod := circle_real_multiply_weak_deriv T h h₁ hh hreal h₁real f (f₁-z • f) hf
  unfold HasWeakCircleShiftedDeriv
  convert hprod using 1
  simp only [map_sub,map_smul]
  abel

theorem circle_shifted_derivative_norm_sq_product (z : ℂ) (hz : conj z = -z)
    (f f₁ f₂ : CircleL2 T)
    (hf : HasWeakCircleShiftedDeriv T z f f₁)
    (hf₁ : HasWeakCircleShiftedDeriv T z f₁ f₂) :
    ‖f₁‖^2 ≤ ‖f‖*‖f₂‖ := by
  have he := circle_shifted_integration_by_parts T z hz f f₁ f₁ f₂ hf hf₁
  calc
    ‖f₁‖^2 = (inner ℂ f₁ f₁).re := norm_sq_eq_re_inner (𝕜 := ℂ) f₁
    _ = (-inner ℂ f f₂).re := congrArg Complex.re he
    _ ≤ ‖-inner ℂ f f₂‖ := Complex.re_le_norm _
    _ = ‖inner ℂ f f₂‖ := norm_neg _
    _ ≤ ‖f‖*‖f₂‖ := norm_inner_le_norm _ _

theorem circle_shifted_fourth_pairing (z : ℂ) (hz : conj z = -z)
    (f f₁ f₂ f₃ f₄ : CircleL2 T)
    (hf : HasWeakCircleShiftedDeriv T z f f₁)
    (hf₁ : HasWeakCircleShiftedDeriv T z f₁ f₂)
    (hf₂ : HasWeakCircleShiftedDeriv T z f₂ f₃)
    (hf₃ : HasWeakCircleShiftedDeriv T z f₃ f₄) :
    inner ℂ f f₄ = inner ℂ f₂ f₂ := by
  have ha := circle_shifted_integration_by_parts T z hz f f₁ f₃ f₄ hf hf₃
  have hb := circle_shifted_integration_by_parts T z hz f₁ f₂ f₂ f₃ hf₁ hf₂
  rw [ha,neg_neg] at hb
  exact hb.symm

theorem circle_shifted_skew_energy (z : ℂ) (hz : conj z = -z)
    (h h₁ : C(AddCircle T, ℂ)) (hh : HasCircleDeriv T h h₁)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (f f₁ : CircleL2 T) (hf : HasWeakCircleShiftedDeriv T z f f₁) :
    (inner ℂ f (circleMultiplyL2 T h f₁+(1/2:ℂ) • circleMultiplyL2 T h₁ f)).re = 0 := by
  have hi := circle_shifted_integration_by_parts T z hz f f₁ (circleMultiplyL2 T h f)
    (circleMultiplyL2 T h f₁+circleMultiplyL2 T h₁ f) hf
    (circle_shifted_multiply_weak_deriv T z h h₁ hh hreal h₁real f f₁ hf)
  rw [inner_add_right] at hi
  have hr := congrArg Complex.re hi
  have hs := circle_multiply_real_pairing T h hreal f f₁
  simp only [Complex.neg_re,Complex.add_re] at hr
  rw [inner_add_right,inner_smul_right]
  simp only [Complex.add_re,Complex.mul_re]
  norm_num
  linarith

end Lemniscate
