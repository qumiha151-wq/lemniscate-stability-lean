import Lemniscate.PeriodicH4Domain

/-! The linear differential expressions as maps from an explicit H4 submodule
to L2. Their values and energy are independent of the selected derivative
witnesses. This is not yet a closedness, adjoint-domain or resolvent theorem. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleH4SymmetricOperator (h h₁ h₂ : C(AddCircle T, ℂ)) :
    circleH4Domain T →ₗ[ℂ] CircleL2 T :=
  (-4:ℂ) • circleH4Derivative T 3 - (45:ℂ) •
    ((circleMultiplyL2 T h₁).toLinearMap.comp (circleH4Derivative T 0) +
      (circleMultiplyL2 T h).toLinearMap.comp (circleH4Derivative T 1)) -
    (42:ℂ) • (circleH4Domain T).subtype +
    (15/4:ℂ) • (circleMultiplyL2 T h₂).toLinearMap.comp (circleH4Domain T).subtype

noncomputable def circleH4Operator (h h₁ h₂ : C(AddCircle T, ℂ)) :
    circleH4Domain T →ₗ[ℂ] CircleL2 T :=
  circleH4SymmetricOperator T h h₁ h₂ + (15/2:ℂ) •
    ((circleMultiplyL2 T h₁).toLinearMap.comp (circleH4Derivative T 0) +
      (1/2:ℂ) • (circleMultiplyL2 T h₂).toLinearMap.comp (circleH4Domain T).subtype)

theorem circle_h4_symmetric_operator_apply (h h₁ h₂ : C(AddCircle T, ℂ))
    (f : circleH4Domain T) :
    circleH4SymmetricOperator T h h₁ h₂ f = circleSymmetricL2Expression T h h₁ h₂
      (f : CircleL2 T) (circleH4Jet T f).first (circleH4Jet T f).second
        (circleH4Jet T f).fourth := rfl

theorem circle_h4_operator_apply (h h₁ h₂ : C(AddCircle T, ℂ)) (f : circleH4Domain T) :
    circleH4Operator T h h₁ h₂ f = circleLinearL2Expression T h h₁ h₂
      (f : CircleL2 T) (circleH4Jet T f).first (circleH4Jet T f).second
        (circleH4Jet T f).fourth := rfl

theorem circle_h4_operator_energy (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) (f : circleH4Domain T) :
    (inner ℂ (f : CircleL2 T) (circleH4Operator T h h₁ h₂ f)).re =
      circleH2Energy T h h₂ (f : CircleL2 T) (circleH4Jet T f).first
        (circleH4Jet T f).second := by
  rw [circle_h4_operator_apply]
  exact circle_weak_linear_energy T h h₁ h₂ hh hh₁ hreal h₁real h₂real
    _ _ _ (circleH4Jet T f).third _ (circleH4Jet T f).hfirst
    (circleH4Jet T f).hsecond (circleH4Jet T f).hthird (circleH4Jet T f).hfourth

theorem circle_h4_operator_cosine_dissipative (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (f : circleH4Domain T)
    (v : CosineSequenceSpace) (hv : (f : CircleL2 T) = circleEvenCosineSynthesis T v) :
    (inner ℂ (f : CircleL2 T) (circleH4Operator T h h₁ h₂ f)).re ≤
      -(21/4:ℝ)*‖(f : CircleL2 T)‖^2 := by
  rw [circle_h4_operator_energy T h h₁ h₂ hh hh₁ hreal h₁real h₂real]
  have hb := circle_cosine_weak_energy_dissipative T h h₁ h₂ hh hh₁ hs hc hr
    v (circleH4Jet T f).first (circleH4Jet T f).second
    (by simpa only [← hv] using (circleH4Jet T f).hfirst) (circleH4Jet T f).hsecond
  simpa only [← hv] using hb

theorem circle_classical_mem_h4 (f f₁ f₂ f₃ f₄ : C(AddCircle T, ℂ))
    (hf : HasCircleDeriv T f f₁) (hf₁ : HasCircleDeriv T f₁ f₂)
    (hf₂ : HasCircleDeriv T f₂ f₃) (hf₃ : HasCircleDeriv T f₃ f₄) :
    InCircleH4 T (circleContinuousL2 T f) :=
  ⟨circleContinuousL2 T f₁, circleContinuousL2 T f₂,
    circleContinuousL2 T f₃, circleContinuousL2 T f₄,
    circle_classical_weak_deriv T f f₁ hf, circle_classical_weak_deriv T f₁ f₂ hf₁,
    circle_classical_weak_deriv T f₂ f₃ hf₂, circle_classical_weak_deriv T f₃ f₄ hf₃⟩

end Lemniscate
