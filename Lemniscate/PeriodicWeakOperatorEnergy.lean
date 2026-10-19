import Lemniscate.PeriodicWeakCalculus

/-! The fourth-order expressions and their energy identities on four successive
L2 weak derivatives. This treats the differential expressions on their natural
weak derivative domain; closedness and adjoint-domain equality are not asserted. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

def InCircleH4 (f : CircleL2 T) : Prop :=
  ∃ f₁ f₂ f₃ f₄ : CircleL2 T, HasWeakCircleDeriv T f f₁ ∧
    HasWeakCircleDeriv T f₁ f₂ ∧ HasWeakCircleDeriv T f₂ f₃ ∧ HasWeakCircleDeriv T f₃ f₄

noncomputable def circleSymmetricL2Expression (h h₁ h₂ : C(AddCircle T, ℂ))
    (f f₁ f₂ f₄ : CircleL2 T) : CircleL2 T :=
  (-4:ℂ) • f₄ - (45:ℂ) • (circleMultiplyL2 T h₁ f₁+circleMultiplyL2 T h f₂) -
    (42:ℂ) • f + (15/4:ℂ) • circleMultiplyL2 T h₂ f

theorem circle_weak_fourth_pairing (f f₁ f₂ f₃ f₄ : CircleL2 T)
    (hf : HasWeakCircleDeriv T f f₁) (hf₁ : HasWeakCircleDeriv T f₁ f₂)
    (hf₂ : HasWeakCircleDeriv T f₂ f₃) (hf₃ : HasWeakCircleDeriv T f₃ f₄) :
    inner ℂ f f₄ = inner ℂ f₂ f₂ := by
  have ha := circle_weak_integration_by_parts T f f₁ f₃ f₄ hf hf₃
  have hb := circle_weak_integration_by_parts T f₁ f₂ f₂ f₃ hf₁ hf₂
  rw [ha, neg_neg] at hb
  exact hb.symm

theorem circle_weak_symmetric_energy (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (f f₁ f₂ f₃ f₄ : CircleL2 T)
    (hf : HasWeakCircleDeriv T f f₁) (hf₁ : HasWeakCircleDeriv T f₁ f₂)
    (hf₂ : HasWeakCircleDeriv T f₂ f₃) (hf₃ : HasWeakCircleDeriv T f₃ f₄) :
    (inner ℂ f (circleSymmetricL2Expression T h h₁ h₂ f f₁ f₂ f₄)).re =
      circleH2Energy T h h₂ f f₁ f₂ := by
  have hfourth := circle_weak_fourth_pairing T f f₁ f₂ f₃ f₄ hf hf₁ hf₂ hf₃
  have hd := circle_weak_integration_by_parts T f f₁ (circleMultiplyL2 T h f₁)
    (circleMultiplyL2 T h f₂+circleMultiplyL2 T h₁ f₁) hf
    (circle_real_multiply_weak_deriv T h h₁ hh hreal h₁real f₁ f₂ hf₁)
  have hdiv : inner ℂ f (circleMultiplyL2 T h₁ f₁+circleMultiplyL2 T h f₂) =
      -inner ℂ f₁ (circleMultiplyL2 T h f₁) := by
    rw [add_comm]
    exact neg_eq_iff_eq_neg.mp hd.symm
  unfold circleSymmetricL2Expression circleH2Energy
  apply congrArg Complex.re
  simp only [inner_add_right, inner_sub_right, inner_smul_right]
  simp only [inner_add_right] at hdiv
  rw [hfourth, hdiv]
  ring

noncomputable def circleLinearL2Expression (h h₁ h₂ : C(AddCircle T, ℂ))
    (f f₁ f₂ f₄ : CircleL2 T) : CircleL2 T :=
  circleSymmetricL2Expression T h h₁ h₂ f f₁ f₂ f₄ +
    (15/2:ℂ) • (circleMultiplyL2 T h₁ f₁+(1/2:ℂ) • circleMultiplyL2 T h₂ f)

theorem circle_weak_linear_energy (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) (f f₁ f₂ f₃ f₄ : CircleL2 T)
    (hf : HasWeakCircleDeriv T f f₁) (hf₁ : HasWeakCircleDeriv T f₁ f₂)
    (hf₂ : HasWeakCircleDeriv T f₂ f₃) (hf₃ : HasWeakCircleDeriv T f₃ f₄) :
    (inner ℂ f (circleLinearL2Expression T h h₁ h₂ f f₁ f₂ f₄)).re =
      circleH2Energy T h h₂ f f₁ f₂ := by
  have hk := circle_weak_skew_energy T h₁ h₂ hh₁ h₁real h₂real f f₁ hf
  have hs := circle_weak_symmetric_energy T h h₁ h₂ hh hreal h₁real
    f f₁ f₂ f₃ f₄ hf hf₁ hf₂ hf₃
  unfold circleLinearL2Expression
  rw [inner_add_right, inner_smul_right, Complex.add_re, Complex.mul_re]
  norm_num
  rw [hk, hs]
  ring

theorem circle_weak_linear_cosine_dissipative (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (v : CosineSequenceSpace)
    (f₁ f₂ f₃ f₄ : CircleL2 T)
    (hf : HasWeakCircleDeriv T (circleEvenCosineSynthesis T v) f₁)
    (hf₁ : HasWeakCircleDeriv T f₁ f₂) (hf₂ : HasWeakCircleDeriv T f₂ f₃)
    (hf₃ : HasWeakCircleDeriv T f₃ f₄) :
    (inner ℂ (circleEvenCosineSynthesis T v)
      (circleLinearL2Expression T h h₁ h₂ (circleEvenCosineSynthesis T v) f₁ f₂ f₄)).re ≤
        -(21/4:ℝ)*‖circleEvenCosineSynthesis T v‖^2 := by
  rw [circle_weak_linear_energy T h h₁ h₂ hh hh₁ hreal h₁real h₂real
    _ f₁ f₂ f₃ f₄ hf hf₁ hf₂ hf₃]
  exact circle_cosine_weak_energy_dissipative T h h₁ h₂ hh hh₁ hs hc hr v f₁ f₂ hf hf₁

end Lemniscate
