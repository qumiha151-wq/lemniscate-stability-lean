import Lemniscate.PeriodicReflection
import Mathlib.Tactic.Module

/-! The actual Bloch differential expression on the fixed periodic H4 domain:
replace each derivative by D+z, then take z=i(2π/T)α. Its quartic dependence
on α is an identity of differential expressions, not a formal matrix ansatz. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleShiftedFirst (z : ℂ) : circleH4Domain T →ₗ[ℂ] CircleL2 T :=
  circleH4Derivative T 0+z • (circleH4Domain T).subtype

noncomputable def circleShiftedSecond (z : ℂ) : circleH4Domain T →ₗ[ℂ] CircleL2 T :=
  circleH4Derivative T 1+(2*z) • circleH4Derivative T 0+z^2 • (circleH4Domain T).subtype

noncomputable def circleShiftedFourth (z : ℂ) : circleH4Domain T →ₗ[ℂ] CircleL2 T :=
  circleH4Derivative T 3+(4*z) • circleH4Derivative T 2+
    (6*z^2) • circleH4Derivative T 1+(4*z^3) • circleH4Derivative T 0+
    z^4 • (circleH4Domain T).subtype

noncomputable def circleBlochOperator (h h₁ h₂ : C(AddCircle T, ℂ)) (α : ℝ) :
    circleH4Domain T →ₗ[ℂ] CircleL2 T :=
  let z := (α:ℂ)*circleFrequencyFactor T 1
  (-4:ℂ) • circleShiftedFourth T z-
    (45:ℂ) • (circleMultiplyL2 T h).toLinearMap.comp (circleShiftedSecond T z)-
    (75/2:ℂ) • (circleMultiplyL2 T h₁).toLinearMap.comp (circleShiftedFirst T z)-
    (42:ℂ) • (circleH4Domain T).subtype+
    (15/2:ℂ) • (circleMultiplyL2 T h₂).toLinearMap.comp (circleH4Domain T).subtype

noncomputable def circleBlochCoefficient (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 5) : circleH4Domain T →ₗ[ℂ] CircleL2 T :=
  let c := circleFrequencyFactor T 1
  ![circleH4Operator T h h₁ h₂,
    c • ((-16:ℂ) • circleH4Derivative T 2-
      (90:ℂ) • (circleMultiplyL2 T h).toLinearMap.comp (circleH4Derivative T 0)-
      (75/2:ℂ) • (circleMultiplyL2 T h₁).toLinearMap.comp (circleH4Domain T).subtype),
    c^2 • ((-24:ℂ) • circleH4Derivative T 1-
      (45:ℂ) • (circleMultiplyL2 T h).toLinearMap.comp (circleH4Domain T).subtype),
    c^3 • ((-16:ℂ) • circleH4Derivative T 0),
    c^4 • ((-4:ℂ) • (circleH4Domain T).subtype)] j

theorem circle_bloch_coefficient_zero (h h₁ h₂ : C(AddCircle T, ℂ)) :
    circleBlochCoefficient T h h₁ h₂ 0 = circleH4Operator T h h₁ h₂ := rfl

theorem circle_bloch_polynomial (h h₁ h₂ : C(AddCircle T, ℂ)) (α : ℝ)
    (f : circleH4Domain T) :
    circleBlochOperator T h h₁ h₂ α f =
      circleBlochCoefficient T h h₁ h₂ 0 f+
      (α:ℂ) • circleBlochCoefficient T h h₁ h₂ 1 f+
      (α:ℂ)^2 • circleBlochCoefficient T h h₁ h₂ 2 f+
      (α:ℂ)^3 • circleBlochCoefficient T h h₁ h₂ 3 f+
      (α:ℂ)^4 • circleBlochCoefficient T h h₁ h₂ 4 f := by
  simp only [circleBlochOperator, circleBlochCoefficient, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    circleShiftedFirst, circleShiftedSecond, circleShiftedFourth,
    circle_h4_operator_expanded, map_add, map_smul]
  change (-4:ℂ) • ((circleH4Jet T f).fourth+
      (4*((α:ℂ)*circleFrequencyFactor T 1)) • (circleH4Jet T f).third+
      (6*((α:ℂ)*circleFrequencyFactor T 1)^2) • (circleH4Jet T f).second+
      (4*((α:ℂ)*circleFrequencyFactor T 1)^3) • (circleH4Jet T f).first+
      ((α:ℂ)*circleFrequencyFactor T 1)^4 • (f : CircleL2 T)) - _ - _ - _ + _ = _
  simp only [show circleH4Derivative T 0 f = (circleH4Jet T f).first from rfl,
    show circleH4Derivative T 1 f = (circleH4Jet T f).second from rfl,
    show circleH4Derivative T 2 f = (circleH4Jet T f).third from rfl,
    show (circleH4Domain T).subtype f = (f : CircleL2 T) from rfl]
  module

theorem circle_bloch_at_zero (h h₁ h₂ : C(AddCircle T, ℂ)) :
    circleBlochOperator T h h₁ h₂ 0 = circleH4Operator T h h₁ h₂ := by
  ext f
  rw [circle_bloch_polynomial, circle_bloch_coefficient_zero]
  simp

end Lemniscate
