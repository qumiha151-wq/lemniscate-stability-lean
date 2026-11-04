import Lemniscate.PeriodicSobolevH4Jet
import Lemniscate.PeriodicH4Operator
import Mathlib.Tactic.Module

/-! The linearized operator is the fourth derivative plus a bounded H2 lower-order map. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

/-- The complete lower-order part, with the true H2 norm on its source. -/
def circleSobolevLowerOrderOperator (h h₁ h₂ : C(AddCircle T, ℂ)) :
    CircleSobolevSpace T 2 →L[ℂ] CircleL2 T :=
  (-45:ℂ) • (circleMultiplyL2 T h).comp (circleSobolevCoordinate T 2 2)-
    (75/2:ℂ) • (circleMultiplyL2 T h₁).comp (circleSobolevCoordinate T 2 1)-
    (42:ℂ) • circleSobolevCoordinate T 2 0+
    (15/2:ℂ) • (circleMultiplyL2 T h₂).comp (circleSobolevCoordinate T 2 0)

def circleSobolevOperator (h h₁ h₂ : C(AddCircle T, ℂ)) :
    CircleSobolevSpace T 4 →L[ℂ] CircleL2 T :=
  (-4:ℂ) • circleSobolevCoordinate T 4 4+
    (circleSobolevLowerOrderOperator T h h₁ h₂).comp
      ((circleSobolevInclusion T 2).comp (circleSobolevInclusion T 3))

theorem circle_sobolev_operator_lower_order (h h₁ h₂ : C(AddCircle T, ℂ))
    (f : CircleSobolevSpace T 4) :
    circleSobolevOperator T h h₁ h₂ f =
      (-4:ℂ) • circleSobolevCoordinate T 4 4 f+
        circleSobolevLowerOrderOperator T h h₁ h₂
          (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)) := rfl

theorem circle_sobolev_operator_eq_h4 (h h₁ h₂ : C(AddCircle T, ℂ))
    (f : CircleSobolevSpace T 4) :
    circleSobolevOperator T h h₁ h₂ f =
      circleH4Operator T h h₁ h₂ (circleSobolevToH4Domain T f) := by
  rw [circle_h4_operator_apply,circle_sobolev_h4_jet]
  simp only [circleSobolevOperator,circleSobolevLowerOrderOperator,
    circleLinearL2Expression,circleSymmetricL2Expression,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    circle_sobolev_inclusion_coordinate,circle_sobolev_to_h4_domain_coe]
  simp [circle_sobolev_coordinate_apply] <;> module

/-- The profile expression uses only coefficient algebra; no profile ODE is
needed for this identification of the bounded linear map. -/
theorem circle_sobolev_operator_profile (q p : C(AddCircle T, ℂ))
    (f : CircleSobolevSpace T 4) :
    circleSobolevOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) f =
      (-4:ℂ) • circleSobolevCoordinate T 4 4 f-
      (45:ℂ) • circleMultiplyL2 T (q^2) (circleSobolevCoordinate T 4 2 f)-
      (75:ℂ) • circleMultiplyL2 T (q*p) (circleSobolevCoordinate T 4 1 f)-
      (69/2:ℂ) • circleSobolevCoordinate T 4 0 f-
      (45/2:ℂ) • circleMultiplyL2 T (q^4) (circleSobolevCoordinate T 4 0 f) := by
  simp only [circleSobolevOperator,circleSobolevLowerOrderOperator,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    circle_sobolev_inclusion_coordinate,circle_multiply_l2_smul_coefficient,
    circle_multiply_l2_sub_coefficient,circle_multiply_l2_one]
  simp [circle_sobolev_coordinate_apply] <;> module

end Lemniscate
