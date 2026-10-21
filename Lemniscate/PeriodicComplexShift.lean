import Lemniscate.PeriodicFullResolvent

/-! Factorization at arbitrary complex parameters through one actual compact
resolvent. This prepares the Fredholm alternative without treating the
unbounded differential operator as a bounded endomorphism of L2. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleComplexShift (h h₁ h₂ : C(AddCircle T, ℂ)) (z : ℂ) :
    circleH4Domain T →ₗ[ℂ] CircleL2 T :=
  z • (circleH4Domain T).subtype - circleH4Operator T h h₁ h₂

theorem circle_complex_shift_real (h h₁ h₂ : C(AddCircle T, ℂ)) (r : ℝ) :
    circleComplexShift T h h₁ h₂ (r:ℂ) = circleFullShift T h h₁ h₂ r := rfl

noncomputable def circleResolventFeedback (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p)
    (hK : ‖circleLowerResolvent T h h₁ h₂ p hp‖ < 1) (z : ℂ) :
    CircleL2 T →L[ℂ] CircleL2 T :=
  (((p^2:ℝ):ℂ)-z) • circleFullResolvent T h h₁ h₂ p hp hK

theorem circle_full_resolvent_h4_left_inverse (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p)
    (hK : ‖circleLowerResolvent T h h₁ h₂ p hp‖ < 1) (u : circleH4Domain T) :
    circleFullResolventH4 T h h₁ h₂ p hp hK
      (circleFullShift T h h₁ h₂ (p^2) u) = u := by
  apply Subtype.ext
  exact circle_full_resolvent_left_inverse T h h₁ h₂ p hp hK u

theorem circle_complex_shift_resolvent (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p)
    (hK : ‖circleLowerResolvent T h h₁ h₂ p hp‖ < 1)
    (z : ℂ) (f : CircleL2 T) :
    circleComplexShift T h h₁ h₂ z (circleFullResolventH4 T h h₁ h₂ p hp hK f) =
      (1-circleResolventFeedback T h h₁ h₂ p hp hK z) f := by
  have hi := circle_full_resolvent_right_inverse T h h₁ h₂ p hp hK f
  have hu : (circleFullResolventH4 T h h₁ h₂ p hp hK f : CircleL2 T) =
      circleFullResolvent T h h₁ h₂ p hp hK f := rfl
  calc
    _ = circleFullShift T h h₁ h₂ (p^2)
          (circleFullResolventH4 T h h₁ h₂ p hp hK f) +
        (z-((p^2:ℝ):ℂ)) •
          (circleFullResolventH4 T h h₁ h₂ p hp hK f : CircleL2 T) := by
      simp only [circleComplexShift, circleFullShift, LinearMap.sub_apply,
        LinearMap.smul_apply, Submodule.subtype_apply]
      module
    _ = f+(z-((p^2:ℝ):ℂ)) • (circleFullResolvent T h h₁ h₂ p hp hK f) := by rw [hi, hu]
    _ = _ := by
      simp only [circleResolventFeedback, sub_apply, one_apply_eq_self, smul_apply]
      module

theorem circle_complex_shift_factorization (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p)
    (hK : ‖circleLowerResolvent T h h₁ h₂ p hp‖ < 1)
    (z : ℂ) (u : circleH4Domain T) :
    circleComplexShift T h h₁ h₂ z u =
      (1-circleResolventFeedback T h h₁ h₂ p hp hK z)
        (circleFullShift T h h₁ h₂ (p^2) u) := by
  have he := circle_complex_shift_resolvent T h h₁ h₂ p hp hK z
    (circleFullShift T h h₁ h₂ (p^2) u)
  rw [circle_full_resolvent_h4_left_inverse] at he
  exact he

theorem circle_resolvent_feedback_compact (h h₁ h₂ : C(AddCircle T, ℂ))
    (p : ℝ) (hp : 1 ≤ p)
    (hK : ‖circleLowerResolvent T h h₁ h₂ p hp‖ < 1) (z : ℂ) :
    IsCompactOperator (circleResolventFeedback T h h₁ h₂ p hp hK z) := by
  unfold circleResolventFeedback
  exact (circle_full_resolvent_compact T h h₁ h₂ p hp hK).smul (((p^2:ℝ):ℂ)-z)

end Lemniscate
