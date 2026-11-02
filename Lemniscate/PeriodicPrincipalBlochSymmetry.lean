import Lemniscate.PeriodicPrincipalSymmetry
import Lemniscate.PeriodicSymmetryPairing

/-! The principal-coordinate Bloch family has the same reflection symmetry as the differential operator. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

theorem circle_principal_bloch_coefficient_reflect (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (p : ℝ) (hp : 1 ≤ p) (j : Fin 5) (f : CircleL2 T) :
    circlePrincipalBlochCoefficient T h h₁ h₂ p hp j (circleReflect T f) =
      (-1:ℂ)^(j:ℕ) • circleReflect T (circlePrincipalBlochCoefficient T h h₁ h₂ p hp j f) := by
  simp only [circle_principal_bloch_coefficient_apply,circle_principal_resolvent_h4_reflect,
    circle_bloch_coefficient_reflect T h h₁ h₂ hh hh₁ hs]

theorem circle_principal_bloch_family_reflect (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (p : ℝ) (hp : 1 ≤ p) (z : ℂ) (f : CircleL2 T) :
    circlePrincipalBlochFamily T h h₁ h₂ p hp z (circleReflect T f) =
      circleReflect T (circlePrincipalBlochFamily T h h₁ h₂ p hp (-z) f) := by
  simp only [circlePrincipalBlochFamily,add_apply,smul_apply,
    circle_principal_bloch_coefficient_reflect T h h₁ h₂ hh hh₁ hs,
    circle_reflect_add,circle_reflect_smul]
  norm_num only [Fin.val_zero,Fin.val_one,show ((2:Fin 5):ℕ) = 2 from rfl,
    show ((3:Fin 5):ℕ) = 3 from rfl,show ((4:Fin 5):ℕ) = 4 from rfl,pow_zero,pow_one]
  module

theorem circle_principal_normalization_neg_reflect (r : ℝ) (hr : 0 < r)
    (ψ : CircleL2 T) (hψ : circleReflect T ψ = -ψ) (f : CircleL2 T) :
    inner ℂ ψ (circlePrincipalResolvent T r hr (-circleReflect T f)) =
      inner ℂ ψ (circlePrincipalResolvent T r hr f) := by
  rw [map_neg,circle_principal_resolvent_reflect,inner_neg_right,
    ← circle_reflect_selfadjoint,hψ,inner_neg_left,neg_neg]

theorem circle_principal_bloch_family_neg_reflect (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (p : ℝ) (hp : 1 ≤ p) (z : ℂ) (f : CircleL2 T) :
    circlePrincipalBlochFamily T h h₁ h₂ p hp z (-circleReflect T f) =
      -circleReflect T (circlePrincipalBlochFamily T h h₁ h₂ p hp (-z) f) := by
  rw [map_neg,circle_principal_bloch_family_reflect T h h₁ h₂ hh hh₁ hs]

end Lemniscate
