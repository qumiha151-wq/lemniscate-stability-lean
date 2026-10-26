import Lemniscate.PeriodicBlochPolynomial
import Lemniscate.PeriodicReflectionOperator

/-! Reflection parity of all actual Bloch coefficient operators. This yields
the odd-parameter cancellations without introducing a basis-change matrix. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

theorem circle_reflect_h4_coe (f : circleH4Domain T) :
    (circleReflectH4 T f : CircleL2 T) = circleReflect T (f : CircleL2 T) := rfl

theorem circle_reflect_h4_third (f : circleH4Domain T) :
    (circleH4Jet T (circleReflectH4 T f)).third =
      (-1:ℂ) • circleReflect T (circleH4Jet T f).third := by
  apply circle_fourier_ext T
  intro n
  rw [fourier_of_weak_circle_deriv T _ _ (circleH4Jet T (circleReflectH4 T f)).hthird,
    circle_reflect_h4_second, circle_fourierCoeff_smul, circle_reflect_fourier,
    circle_reflect_fourier, fourier_of_weak_circle_deriv T _ _ (circleH4Jet T f).hthird,
    circle_frequency_factor_neg]
  ring

theorem circle_bloch_coefficient_one_apply (h h₁ h₂ : C(AddCircle T, ℂ)) (f : circleH4Domain T) :
    circleBlochCoefficient T h h₁ h₂ 1 f = circleFrequencyFactor T 1 •
      ((-16:ℂ) • (circleH4Jet T f).third-
        (90:ℂ) • circleMultiplyL2 T h (circleH4Jet T f).first-
        (75/2:ℂ) • circleMultiplyL2 T h₁ (f : CircleL2 T)) := rfl

theorem circle_bloch_coefficient_two_apply (h h₁ h₂ : C(AddCircle T, ℂ)) (f : circleH4Domain T) :
    circleBlochCoefficient T h h₁ h₂ 2 f = (circleFrequencyFactor T 1)^2 •
      ((-24:ℂ) • (circleH4Jet T f).second-(45:ℂ) • circleMultiplyL2 T h (f : CircleL2 T)) := rfl

theorem circle_bloch_coefficient_three_apply (h h₁ h₂ : C(AddCircle T, ℂ)) (f : circleH4Domain T) :
    circleBlochCoefficient T h h₁ h₂ 3 f =
      (circleFrequencyFactor T 1)^3 • ((-16:ℂ) • (circleH4Jet T f).first) := rfl

theorem circle_bloch_coefficient_four_apply (h h₁ h₂ : C(AddCircle T, ℂ)) (f : circleH4Domain T) :
    circleBlochCoefficient T h h₁ h₂ 4 f =
      (circleFrequencyFactor T 1)^4 • ((-4:ℂ) • (f : CircleL2 T)) := rfl

theorem circle_bloch_top_coefficient (h h₁ h₂ : C(AddCircle T, ℂ))
    (r : ℝ) (hr : (2*Real.pi/T)^2 = r) (f : circleH4Domain T) :
    circleBlochCoefficient T h h₁ h₂ 4 f = ((-4*r^2 : ℝ) : ℂ) • (f : CircleL2 T) := by
  have hc₂ : (circleFrequencyFactor T 1)^2 = -(r:ℂ) := by
    simpa only [Int.cast_one, one_pow, mul_one, hr, Complex.ofReal_neg] using
      circle_frequency_factor_sq T 1
  have hc₄ : (circleFrequencyFactor T 1)^4 = (r:ℂ)^2 := by
    calc
      _ = ((circleFrequencyFactor T 1)^2)^2 := by ring
      _ = _ := by rw [hc₂, neg_sq]
  rw [circle_bloch_coefficient_four_apply, smul_smul, hc₄]
  congr 1
  push_cast
  ring

theorem circle_bloch_coefficient_reflect (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (j : Fin 5) (f : circleH4Domain T) :
    circleBlochCoefficient T h h₁ h₂ j (circleReflectH4 T f) =
      (-1:ℂ)^(j:ℕ) • circleReflect T (circleBlochCoefficient T h h₁ h₂ j f) := by
  have hs₁ : ∀ n : ℤ, fourierCoeff h₁ (-n) = (-1:ℂ)*fourierCoeff h₁ n := by
    intro n
    exact circle_deriv_reflection_parity T h h₁ hh 1 (by simpa only [one_mul] using hs) n
  have h0 (g : CircleL2 T) : circleReflect T (circleMultiplyL2 T h g) =
      circleMultiplyL2 T h (circleReflect T g) := by
    simpa only [one_smul] using circle_reflect_multiply T h 1
      (by simpa only [one_mul] using hs) g
  have h1 (g : CircleL2 T) := circle_reflect_multiply T h₁ (-1) hs₁ g
  fin_cases j
  · change circleBlochCoefficient T h h₁ h₂ 0 (circleReflectH4 T f) =
      (-1:ℂ)^0 • circleReflect T (circleBlochCoefficient T h h₁ h₂ 0 f)
    rw [circle_bloch_coefficient_zero, pow_zero, one_smul]
    exact circle_h4_operator_reflect_of_even T h h₁ h₂ hh hh₁ hs f
  · change circleBlochCoefficient T h h₁ h₂ 1 (circleReflectH4 T f) =
      (-1:ℂ)^1 • circleReflect T (circleBlochCoefficient T h h₁ h₂ 1 f)
    simp only [circle_bloch_coefficient_one_apply, circle_reflect_smul, circle_reflect_sub,
      circle_reflect_h4_third, circle_reflect_h4_first, circle_reflect_h4_coe,
      h0, h1, map_smul]
    norm_num only [Fin.val_one, pow_one]
    module
  · change circleBlochCoefficient T h h₁ h₂ 2 (circleReflectH4 T f) =
      (-1:ℂ)^2 • circleReflect T (circleBlochCoefficient T h h₁ h₂ 2 f)
    simp only [circle_bloch_coefficient_two_apply, circle_reflect_smul, circle_reflect_sub,
      circle_reflect_h4_second, circle_reflect_h4_coe, h0]
    norm_num
  · change circleBlochCoefficient T h h₁ h₂ 3 (circleReflectH4 T f) =
      (-1:ℂ)^3 • circleReflect T (circleBlochCoefficient T h h₁ h₂ 3 f)
    simp only [circle_bloch_coefficient_three_apply, circle_reflect_smul,
      circle_reflect_h4_first]
    norm_num <;> module
  · change circleBlochCoefficient T h h₁ h₂ 4 (circleReflectH4 T f) =
      (-1:ℂ)^4 • circleReflect T (circleBlochCoefficient T h h₁ h₂ 4 f)
    simp only [circle_bloch_coefficient_four_apply, circle_reflect_smul, circle_reflect_h4_coe]
    norm_num

end Lemniscate
