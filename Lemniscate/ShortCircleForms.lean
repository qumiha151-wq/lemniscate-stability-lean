import Lemniscate.PeriodicExactReducedForm
import Lemniscate.ShortAdjointApproximation

/-! The seven-mode comparison acts on actual periodic functions.
Its neutral vectors are exactly those used in the newly verified matrices. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleShortHouseholder : CircleL2 T →L[ℂ] CircleL2 T :=
  neutralHouseholder (circleShortRotationApproximation T:CircleL2 T)
    (circleHouseholderAnchor T)

noncomputable def circleShortHouseholderH4 (f : circleH4Domain T) : circleH4Domain T :=
  neutralHouseholderDomain (circleShortRotationApproximation T)
    (circleHouseholderAnchorH4 T) f

theorem circle_short_householder_coe (f : circleH4Domain T) :
    (circleShortHouseholderH4 T f:CircleL2 T) = circleShortHouseholder T (f:CircleL2 T) :=
  neutral_householder_domain_coe _ _ f

noncomputable def circleShortTransformedCoefficient (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 5) (f : circleH4Domain T) : CircleL2 T :=
  circleShortHouseholder T
    (neutralTransform (circleShortRotationApproximation T)
      (circleShortAdjointApproximation T:CircleL2 T)
      (circleBlochCoefficient T h h₁ h₂ j
        (neutralTransformInvDomain (circleShortRotationApproximation T)
          (circleShortAdjointApproximation T:CircleL2 T)
          (circleShortHouseholderH4 T f))))

noncomputable def circleShortSymmetricCoefficient (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 5) (f g : circleH4Domain T) : ℂ :=
  if j=0 then
    inner ℂ (circleShortHouseholderH4 T f:CircleL2 T)
      (circleH4SymmetricOperator T h h₁ h₂ (circleShortHouseholderH4 T g))
  else (1/2:ℂ)*(inner ℂ (f:CircleL2 T) (circleShortTransformedCoefficient T h h₁ h₂ j g)+
    inner ℂ (circleShortTransformedCoefficient T h h₁ h₂ j f) (g:CircleL2 T))

/-- Monomial coefficients of the shifted reduced form. Only the first four
input forms are used; the fourth-order principal part is kept exact. -/
noncomputable def circleReducedShiftedCoefficient
    (H : Fin 5 → circleH4Domain T → circleH4Domain T → ℂ)
    (k : Fin 5) (f g : circleH4Domain T) : ℂ :=
  let f₀ := circleFixedProjectionH4 T f
  let g₀ := circleFixedProjectionH4 T g
  let f₁ := f-f₀
  let g₁ := g-g₀
  let c : ℂ := ((-4*(2*Real.pi/T)^4:ℝ):ℂ)
  ![H 0 f₁ g₁+H 1 f₀ g₁+H 1 f₁ g₀+H 2 f₀ g₀+
      (1/2:ℂ)*inner ℂ (f:CircleL2 T) (g:CircleL2 T),
    H 1 f₁ g₁+H 2 f₀ g₁+H 2 f₁ g₀,
    H 2 f₁ g₁+H 3 f₀ g₁+H 3 f₁ g₀+c*inner ℂ (f₀:CircleL2 T) (g₀:CircleL2 T),
    H 3 f₁ g₁,
    c*inner ℂ (f₁:CircleL2 T) (g₁:CircleL2 T)] k

noncomputable def circleShiftedBernsteinPairing
    (H : Fin 5 → circleH4Domain T → circleH4Domain T → ℂ)
    (j : Fin 5) (f g : circleH4Domain T) : ℂ :=
  ∑ k : Fin 5, (shortBernsteinWeight j k:ℂ)*circleReducedShiftedCoefficient T H k f g

noncomputable def circleShortBernsteinPairing (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 5) (f g : circleH4Domain T) : ℂ :=
  circleShiftedBernsteinPairing T (circleShortSymmetricCoefficient T h h₁ h₂) j f g

theorem circle_reduced_shifted_polynomial
    (H : Fin 5 → circleH4Domain T → circleH4Domain T → ℂ)
    (α : ℝ) (f g : circleH4Domain T) :
    circleReducedBlochForm T H α f g+(1/2:ℂ)*inner ℂ (f:CircleL2 T) (g:CircleL2 T) =
      ∑ k : Fin 5, (α:ℂ)^k.val*circleReducedShiftedCoefficient T H k f g := by
  simp only [Fin.sum_univ_succ, circleReducedShiftedCoefficient,
    circleReducedBlochForm, Fin.val_zero, Fin.val_succ]
  norm_num only [Matrix.cons_val_zero, Matrix.cons_val_succ, pow_zero, one_mul,
    Fin.sum_univ_zero, add_zero]
  ring

end Lemniscate
