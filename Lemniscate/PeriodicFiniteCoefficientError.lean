import Lemniscate.PeriodicAuxiliaryHighAction

/-! Exact finite-rank differences between the actual transformed tests
and the symmetric Bloch coefficients. No quantitative error bound is assumed. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleFiniteCoefficientError (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 3) (f : circleH4Domain T) : CircleL2 T :=
  circleFiniteCoefficientTest T h h₁ h₂ (j.castLE (by decide)) f-
    circleBlochSymmetricCoefficient T h h₁ h₂ j f

theorem circle_finite_zero_error_expansion (h h₁ h₂ : C(AddCircle T, ℂ)) (f : circleH4Domain T) :
    circleFiniteCoefficientError T h h₁ h₂ 0 f =
      -((1+inner ℂ (circleFiniteRotationPhase T:CircleL2 T) (circleHouseholderAnchor T))⁻¹*
        inner ℂ ((circleFiniteRotationPhase T:CircleL2 T)+circleHouseholderAnchor T) (f:CircleL2 T)) •
          circleH4SymmetricOperator T h h₁ h₂ (circleFiniteRotationPhase T+circleHouseholderAnchorH4 T) := by
  change circleH4SymmetricOperator T h h₁ h₂
    (neutralHouseholderDomain (circleFiniteRotationPhase T) (circleHouseholderAnchorH4 T) f)-
      circleBlochSymmetricCoefficient T h h₁ h₂ 0 f = _
  rw [circle_bloch_symmetric_coefficient_zero]
  simp only [neutralHouseholderDomain,map_sub,map_smul,circle_householder_anchor_h4_coe]
  module

theorem circle_finite_positive_error_expansion (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 3) (hj : j ≠ 0) (f : circleH4Domain T) :
    let e := circleFiniteRotationPhase T
    let a := circleHouseholderAnchorH4 T
    let z := circleFiniteAdjointPhaseH4 T-e
    let d := 1+inner ℂ (e:CircleL2 T) (a:CircleL2 T)
    let t := inner ℂ ((e:CircleL2 T)+(a:CircleL2 T)) (f:CircleL2 T)
    let b := inner ℂ (e:CircleL2 T) (neutralHouseholderAdjointDomain e a f:CircleL2 T)
    let c := inner ℂ (z:CircleL2 T) (neutralHouseholderDomain e a f:CircleL2 T)
    let A := circleBlochCoefficient T h h₁ h₂ (j.castLE (by decide))
    let Astar := circleBlochAdjointCoefficient T h h₁ h₂ (j.castLE (by decide))
    circleFiniteCoefficientError T h h₁ h₂ j f =
      (-(1/2:ℂ)*(conj d)⁻¹*t) • Astar (e+a)+
      (-(1/2:ℂ)*d⁻¹*t) • A (e+a)+
      ((1/2:ℂ)*b) • Astar z+(-(1/2:ℂ)*c) • A e := by
  have hj' : (j.castLE (by decide):Fin 5) ≠ 0 := by
    intro heq
    apply hj
    apply Fin.ext
    exact congrArg (fun k : Fin 5 => k.val) heq
  dsimp only [circleFiniteCoefficientError,circleFiniteCoefficientTest,
    circleBlochSymmetricCoefficient]
  simp only [if_neg hj']
  dsimp only [LinearMap.smul_apply,LinearMap.add_apply,
    circleFiniteLeftAdjointDomain,LinearMap.comp_apply,neutralTransformAdjointDomain,
    circleFiniteRightInput,neutralTransformInvDomain,neutralHouseholderDomain,
    neutralHouseholderAdjointDomain,LinearMap.coe_mk,AddHom.coe_mk]
  simp only [map_add,map_sub,map_smul,Submodule.coe_sub,Submodule.coe_add,
    Submodule.coe_smul_of_tower,circle_finite_adjoint_phase_h4_coe,
    circle_householder_anchor_h4_coe,map_inv₀,map_one]
  module

end Lemniscate
