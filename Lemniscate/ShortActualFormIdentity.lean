import Lemniscate.ShortCircleForms
import Lemniscate.ShortNeutralComparison
import Lemniscate.NeutralTransformAdjoints

/-! Actual pairing identities for the new low-order form comparison.
The common phase cancels in the two neutral changes of variables. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

theorem short_neutral_inverse_phase (e : circleH4Domain T) (ψ : CircleL2 T)
    (f : circleH4Domain T) :
    neutralTransformInvDomain ((-I) • e) ((-I) • ψ) f =
      neutralTransformInvDomain e ψ f := by
  apply Subtype.ext
  rw [neutral_transform_inv_domain_coe,neutral_transform_inv_domain_coe,
    circle_neutral_inverse_common_phase]

theorem short_transformed_pairing (e a ψ f : circleH4Domain T)
    (hea : inner ℂ (a:CircleL2 T) (e:CircleL2 T) =
      inner ℂ (e:CircleL2 T) (a:CircleL2 T)) (v : CircleL2 T) :
    inner ℂ (f:CircleL2 T)
      (neutralHouseholder (e:CircleL2 T) (a:CircleL2 T)
        (neutralTransform e (ψ:CircleL2 T) v)) =
      inner ℂ (shortLeftInput e ψ (neutralHouseholderDomain e a f):CircleL2 T) v := by
  rw [← neutral_householder_selfadjoint (e:CircleL2 T) (a:CircleL2 T) hea,
    ← neutral_householder_domain_coe]
  exact (neutral_transform_adjoint_domain_green e ψ
    (neutralHouseholderDomain e a f) v).symm

theorem short_exact_positive_pairing
    (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)
    (ψ : circleH4Domain T) (j : Fin 5) (f g : circleH4Domain T) :
    let e := circleShortRotationVector T q p hq hp
    let φ := circleShortAdjointVector T ψ
    let U := circleRotationHouseholderH4 T q p hq hp
    inner ℂ (f:CircleL2 T) (circleCenteredBlochCoefficient T q p hq hp (ψ:CircleL2 T) j g) =
      inner ℂ (shortLeftInput e φ (U f):CircleL2 T)
        (circleBlochCoefficient T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) j
          (shortRightInput e φ (U g))) := by
  dsimp only
  let e := circleShortRotationVector T q p hq hp
  let φ := circleShortAdjointVector T ψ
  let a := circleHouseholderAnchorH4 T
  let U := circleRotationHouseholderH4 T q p hq hp
  have hphase : shortRightInput e φ (U g) =
      neutralTransformInvDomain (circleUnitRotationH4 T q p hq hp) (ψ:CircleL2 T) (U g) :=
    short_neutral_inverse_phase T _ _ _
  have hea := (paper_rotation_householder_hypotheses T q p hq hp he hqreal hpreal hs hc ho hr).2.1
  change inner ℂ (f:CircleL2 T) (circleRotationHouseholder T q p
    (neutralTransform (circleUnitRotationH4 T q p hq hp) (ψ:CircleL2 T)
      (circleBlochCoefficient T _ _ _ j
        (neutralTransformInvDomain _ _ (U g))))) = _
  rw [← hphase,← circle_neutral_transform_common_phase T
    (circleUnitRotationH4 T q p hq hp) (ψ:CircleL2 T)]
  exact short_transformed_pairing T e a φ f hea _

theorem short_finite_positive_pairing (h h₁ h₂ : C(AddCircle T, ℂ))
    (hea : inner ℂ (circleHouseholderAnchor T) (circleShortRotationApproximation T:CircleL2 T) =
      inner ℂ (circleShortRotationApproximation T:CircleL2 T) (circleHouseholderAnchor T))
    (j : Fin 5) (f g : circleH4Domain T) :
    inner ℂ (f:CircleL2 T) (circleShortTransformedCoefficient T h h₁ h₂ j g) =
      inner ℂ (shortLeftInput (circleShortRotationApproximation T)
        (circleShortAdjointApproximation T) (circleShortHouseholderH4 T f):CircleL2 T)
        (circleBlochCoefficient T h h₁ h₂ j
          (shortRightInput (circleShortRotationApproximation T)
            (circleShortAdjointApproximation T) (circleShortHouseholderH4 T g))) := by
  unfold circleShortTransformedCoefficient circleShortHouseholder circleShortHouseholderH4
  generalize he : circleShortRotationApproximation T = e at *
  generalize hp : circleShortAdjointApproximation T = p at *
  exact short_transformed_pairing T e (circleHouseholderAnchorH4 T) p f hea
    (circleBlochCoefficient T h h₁ h₂ j
      (shortRightInput e p (neutralHouseholderDomain e (circleHouseholderAnchorH4 T) g)))

end Lemniscate
