import Lemniscate.PeriodicLinearEnergy

/-! Integration by parts between two L2 weak derivative chains, and a weak
product rule for real C1 coefficients. These avoid a classical regularity
assumption on the functions to which the differential operator is applied. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_weak_integration_by_parts (f f₁ g g₁ : CircleL2 T)
    (hf : HasWeakCircleDeriv T f f₁) (hg : HasWeakCircleDeriv T g g₁) :
    inner ℂ f₁ g = -inner ℂ f g₁ := by
  have hi := circle_complex_multiplier_duality T f f₁ g ((-1:ℂ) • g₁)
    (circleFrequencyFactor T) (fourier_of_weak_circle_deriv T f f₁ hf) (by
      intro n
      rw [circle_fourierCoeff_smul, fourier_of_weak_circle_deriv T g g₁ hg,
        circle_frequency_factor_conj]
      ring)
  simpa only [inner_smul_right, neg_one_mul] using hi

theorem circle_real_multiply_weak_deriv (h h₁ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (f f₁ : CircleL2 T) (hf : HasWeakCircleDeriv T f f₁) :
    HasWeakCircleDeriv T (circleMultiplyL2 T h f)
      (circleMultiplyL2 T h f₁+circleMultiplyL2 T h₁ f) := by
  intro φ φ₁ hφ
  have hi := hf (h*φ) (h₁*φ+h*φ₁) (circle_deriv_mul T h h₁ φ φ₁ hh hφ)
  have hl : circleContinuousL2 T (h₁*φ+h*φ₁) =
      circleContinuousL2 T (h₁*φ)+circleContinuousL2 T (h*φ₁) := by
    simp only [circleContinuousL2, map_add]
  rw [hl, inner_add_right, ← circle_multiply_l2_continuous,
    ← circle_multiply_l2_continuous, ← circle_multiply_l2_continuous] at hi
  rw [inner_add_left, circle_multiply_l2_symmetric T h hreal,
    circle_multiply_l2_symmetric T h₁ h₁real, circle_multiply_l2_symmetric T h hreal,
    hi]
  ring

theorem circle_weak_skew_energy (h h₁ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (f f₁ : CircleL2 T) (hf : HasWeakCircleDeriv T f f₁) :
    (inner ℂ f (circleMultiplyL2 T h f₁+(1/2:ℂ) • circleMultiplyL2 T h₁ f)).re = 0 := by
  have hi := circle_weak_integration_by_parts T f f₁ (circleMultiplyL2 T h f)
    (circleMultiplyL2 T h f₁+circleMultiplyL2 T h₁ f) hf
    (circle_real_multiply_weak_deriv T h h₁ hh hreal h₁real f f₁ hf)
  rw [inner_add_right] at hi
  have hr := congrArg Complex.re hi
  have hs := circle_multiply_real_pairing T h hreal f f₁
  simp only [Complex.neg_re, Complex.add_re] at hr
  rw [inner_add_right, inner_smul_right]
  simp only [Complex.add_re, Complex.mul_re]
  norm_num
  linarith

end Lemniscate
