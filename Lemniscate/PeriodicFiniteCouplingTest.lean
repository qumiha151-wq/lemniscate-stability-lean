import Lemniscate.NeutralTransformAdjoints
import Lemniscate.PeriodicBlochGreen
import Lemniscate.PeriodicFiniteBlochForm

/-! Represent the actual low-high coefficient pairing by an L2 test function.
The high input is arbitrary H4; it is not replaced by a finite Fourier sum. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleFiniteAdjointPhaseH4 : circleH4Domain T :=
  I • circleAdjointApproximation T

theorem circle_finite_adjoint_phase_h4_coe :
    (circleFiniteAdjointPhaseH4 T:CircleL2 T) = circleFiniteAdjointPhase T := rfl

noncomputable def circleFiniteLeftAdjointDomain : circleH4Domain T →ₗ[ℂ] circleH4Domain T :=
  (neutralTransformAdjointDomain (circleFiniteRotationPhase T) (circleFiniteAdjointPhaseH4 T)).comp
    (neutralHouseholderAdjointDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T))

noncomputable def circleFiniteRightInput (f : circleH4Domain T) : circleH4Domain T :=
  neutralTransformInvDomain (circleFiniteRotationPhase T) (circleFiniteAdjointPhase T)
    (neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T) f)

theorem circle_finite_householder_high_eq (y : circleH4Domain T)
    (hy : ∀ n : ℤ, |(n:ℝ)| < 32 → fourierCoeff (y:CircleL2 T) n = 0) :
    neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T) y = y := by
  rcases circle_finite_high_pairings T y hy with ⟨he, _, ha⟩
  simp only [neutralHouseholderDomain, circle_householder_anchor_h4_coe,
    inner_add_left, he, ha, add_zero, mul_zero, zero_smul, sub_zero]

theorem circle_finite_right_high_eq (y : circleH4Domain T)
    (hy : ∀ n : ℤ, |(n:ℝ)| < 32 → fourierCoeff (y:CircleL2 T) n = 0) :
    circleFiniteRightInput T y = y := by
  rcases circle_finite_high_pairings T y hy with ⟨he, hp, _⟩
  rw [circleFiniteRightInput, circle_finite_householder_high_eq T y hy]
  simp only [neutralTransformInvDomain, inner_sub_left, hp, he, sub_self, zero_smul, sub_zero]

theorem circle_finite_output_high_pairing (g : CircleL2 T) (y : circleH4Domain T)
    (hy : ∀ n : ℤ, |(n:ℝ)| < 32 → fourierCoeff (y:CircleL2 T) n = 0) :
    inner ℂ (neutralHouseholder (circleFiniteRotationPhase T:CircleL2 T) (circleHouseholderAnchor T)
      (neutralTransform (circleFiniteRotationPhase T) (circleFiniteAdjointPhase T) g)) (y:CircleL2 T) =
      inner ℂ g (y:CircleL2 T) := by
  rcases circle_finite_high_pairings T y hy with ⟨he, _, ha⟩
  simp only [neutral_householder_apply, inner_sub_left, inner_smul_left, inner_add_left,
    he, ha, add_zero, mul_zero, sub_zero]
  rw [neutral_transform_apply, inner_add_left, inner_smul_left, he, mul_zero, add_zero]

noncomputable def circleFiniteCoefficientTest (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 5) (f : circleH4Domain T) : CircleL2 T :=
  if j = 0 then circleH4SymmetricOperator T h h₁ h₂
    (neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T) f)
  else (1/2:ℂ) •
    (circleBlochAdjointCoefficient T h h₁ h₂ j (circleFiniteLeftAdjointDomain T f)+
      circleBlochCoefficient T h h₁ h₂ j (circleFiniteRightInput T f))

theorem circle_finite_coefficient_high_test (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) (j : Fin 5) (f y : circleH4Domain T)
    (hy : ∀ n : ℤ, |(n:ℝ)| < 32 → fourierCoeff (y:CircleL2 T) n = 0) :
    circleFiniteSymmetricCoefficient T h h₁ h₂ j f y =
      inner ℂ (circleFiniteCoefficientTest T h h₁ h₂ j f) (y:CircleL2 T) := by
  by_cases hj : j = 0
  · subst j
    rw [circle_finite_zero_coefficient T h h₁ h₂ hh hh₁ hreal h₁real h₂real,
      circle_finite_householder_high_eq T y hy, circleFiniteCoefficientTest, if_pos rfl]
    exact (circle_h4_symmetric_green T h h₁ h₂ hh hreal h₁real h₂real _ y).symm
  · have hfirst : inner ℂ (f:CircleL2 T)
        (circleFiniteTransformedOperator T (circleBlochCoefficient T h h₁ h₂ j) y) =
        inner ℂ (circleBlochAdjointCoefficient T h h₁ h₂ j (circleFiniteLeftAdjointDomain T f))
          (y:CircleL2 T) := by
      change inner ℂ (f:CircleL2 T)
        (neutralHouseholder (circleFiniteRotationPhase T:CircleL2 T) (circleHouseholderAnchor T)
          (neutralTransform (circleFiniteRotationPhase T) (circleFiniteAdjointPhase T)
            (circleBlochCoefficient T h h₁ h₂ j (circleFiniteRightInput T y)))) = _
      rw [circle_finite_right_high_eq T y hy,
        ← circle_householder_anchor_h4_coe T,
        ← neutral_householder_adjoint_domain_green (circleFiniteRotationPhase T)
          (circleHouseholderAnchorH4 T) f,
        ← circle_finite_adjoint_phase_h4_coe T,
        ← neutral_transform_adjoint_domain_green (circleFiniteRotationPhase T)
          (circleFiniteAdjointPhaseH4 T)]
      have hg := congrArg conj (circle_bloch_coefficient_green T h h₁ h₂
        hh hh₁ hreal h₁real h₂real j y (circleFiniteLeftAdjointDomain T f))
      simpa only [inner_conj_symm, circleFiniteLeftAdjointDomain, LinearMap.comp_apply] using hg
    have hsecond : inner ℂ
        (circleFiniteTransformedOperator T (circleBlochCoefficient T h h₁ h₂ j) f) (y:CircleL2 T) =
        inner ℂ (circleBlochCoefficient T h h₁ h₂ j (circleFiniteRightInput T f)) (y:CircleL2 T) :=
      circle_finite_output_high_pairing T _ y hy
    rw [circleFiniteSymmetricCoefficient, if_neg hj, hfirst, hsecond,
      circleFiniteCoefficientTest, if_neg hj, inner_smul_left, inner_add_left]
    norm_num [map_ofNat]

end Lemniscate
