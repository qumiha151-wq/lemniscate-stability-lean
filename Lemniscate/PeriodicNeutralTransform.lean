import Lemniscate.NeutralTransform
import Lemniscate.PeriodicAdjointReality

/-! The exact neutral change of variables for the actual periodic H4 operator.
Both inverse identities, preservation of the domain, orthogonal compression,
and vanishing neutral row and column are proved before any approximation. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

def HasCircleNeutralDecomposition (h h₁ h₂ : C(AddCircle T, ℂ))
    (e : circleH4Domain T) (ψ : CircleL2 T) : Prop :=
  (∀ f : CircleL2 T,
    neutralTransform e ψ (neutralTransformInv e ψ f) = f ∧
    neutralTransformInv e ψ (neutralTransform e ψ f) = f) ∧
  (∀ f : circleH4Domain T,
    neutralTransformDomain e ψ (neutralTransformInvDomain e ψ f) = f ∧
    neutralTransformInvDomain e ψ (neutralTransformDomain e ψ f) = f) ∧
  (∀ f : circleH4Domain T,
    neutralTransform e ψ (circleH4Operator T h h₁ h₂ (neutralTransformInvDomain e ψ f)) =
      circleH4Operator T h h₁ h₂ f -
        inner ℂ (e : CircleL2 T) (circleH4Operator T h h₁ h₂ f) • (e : CircleL2 T)) ∧
  (∀ f : circleH4Domain T, inner ℂ (e : CircleL2 T)
    (neutralTransform e ψ (circleH4Operator T h h₁ h₂ (neutralTransformInvDomain e ψ f))) = 0) ∧
  neutralTransform e ψ (circleH4Operator T h h₁ h₂ (neutralTransformInvDomain e ψ e)) = 0

theorem circle_neutral_decomposition_of_pairing (h h₁ h₂ : C(AddCircle T, ℂ))
    (e : circleH4Domain T) (ψ : CircleL2 T)
    (hunit : inner ℂ (e : CircleL2 T) (e : CircleL2 T) = 1)
    (he : circleH4Operator T h h₁ h₂ e = 0)
    (hnorm : inner ℂ ψ (e : CircleL2 T) = 1)
    (hψ : ∀ f : circleH4Domain T, inner ℂ ψ (circleH4Operator T h h₁ h₂ f) = 0) :
    HasCircleNeutralDecomposition T h h₁ h₂ e ψ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f
    exact ⟨neutral_transform_right_inverse e ψ hunit hnorm f,
      neutral_transform_left_inverse e ψ hunit hnorm f⟩
  · intro f
    exact ⟨neutral_transform_domain_right_inverse e ψ hunit hnorm f,
      neutral_transform_domain_left_inverse e ψ hunit hnorm f⟩
  · exact neutral_transformed_operator e ψ (circleH4Operator T h h₁ h₂) he hψ
  · exact neutral_transformed_operator_orthogonal e ψ hunit (circleH4Operator T h h₁ h₂) he hψ
  · exact neutral_transformed_operator_neutral e ψ (circleH4Operator T h h₁ h₂) he hψ

theorem circle_neutral_transform_reflect (e : circleH4Domain T) (ψ f : CircleL2 T)
    (he : circleReflect T (e : CircleL2 T) = -(e : CircleL2 T))
    (hψ : circleReflect T ψ = -ψ) :
    neutralTransform e ψ (circleReflect T f) = circleReflect T (neutralTransform e ψ f) := by
  have hz : circleReflect T (ψ-(e : CircleL2 T)) = -(ψ-(e : CircleL2 T)) := by
    rw [circle_reflect_sub, hψ, he]
    abel
  have hp : inner ℂ (ψ-(e : CircleL2 T)) (circleReflect T f) =
      -inner ℂ (ψ-(e : CircleL2 T)) f := by
    rw [← circle_reflect_selfadjoint, hz, inner_neg_left]
  rw [neutral_transform_apply, neutral_transform_apply, circle_reflect_add,
    circle_reflect_smul, he, hp, neg_smul, smul_neg]

noncomputable def circleUnitRotationH4 (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3))) : circleH4Domain T :=
  ((‖circleContinuousL2 T (q*p)‖:ℂ)⁻¹) • circleRotationH4 T q p hq hp

theorem circle_unit_rotation_h4_coe (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3))) :
    (circleUnitRotationH4 T q p hq hp : CircleL2 T) = circleUnitRotation T q p := rfl

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ i : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*i+1) = 0)
    (hr : (2*Real.pi/T)^2 = thetaParameter)

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_single_period_neutral_decomposition :
    ∃ ψ : circleH4Domain T,
      inner ℂ (ψ : CircleL2 T) (circleUnitRotation T q p) = 1 ∧
      circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0 ∧
      circleConjugate T (ψ : CircleL2 T) = (ψ : CircleL2 T) ∧
      InCircleEvenSineSector T (ψ : CircleL2 T) ∧
      HasCircleNeutralDecomposition T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
        (circleUnitRotationH4 T q p hq hp) (ψ : CircleL2 T) := by
  obtain ⟨ψ, hψ, _⟩ :=
    paper_single_period_adjoint_real_sector T q p hq hp he hqreal hpreal hs hc ho hr
  refine ⟨ψ, hψ.1, hψ.2.1, hψ.2.2.1, hψ.2.2.2, ?_⟩
  let N := paperSinglePeriodNeutralOperator T q p hq hp he hqreal hpreal hs hc ho hr
  apply circle_neutral_decomposition_of_pairing
  · exact N.inner_neutral_self
  · exact N.kills_neutral
  · exact hψ.1
  · intro f
    have h0real : ∀ x, conj ((q^2 : C(AddCircle T, ℂ)) x) = (q^2 : C(AddCircle T, ℂ)) x := by
      intro x
      change conj ((q x)^2) = (q x)^2
      simp only [map_pow, hqreal]
    have h1real : ∀ x, conj (((2:ℂ) • (q*p)) x) = ((2:ℂ) • (q*p)) x := by
      intro x
      change conj (2*(q x*p x)) = 2*(q x*p x)
      simp only [map_mul, map_ofNat, hqreal, hpreal]
    have h2real : ∀ x, conj ((1-(3:ℂ) • (q^4) : C(AddCircle T, ℂ)) x) =
        (1-(3:ℂ) • (q^4) : C(AddCircle T, ℂ)) x := by
      intro x
      change conj (1-3*(q x)^4) = 1-3*(q x)^4
      simp only [map_sub, map_mul, map_one, map_ofNat, map_pow, hqreal]
    rw [← inner_conj_symm, circle_h4_formal_adjoint_green T (q^2) ((2:ℂ) • (q*p))
      (1-(3:ℂ) • (q^4)) (circle_profile_square_deriv T q p hq)
      (circle_profile_square_second T q p hq hp he) h0real h1real h2real f ψ,
      hψ.2.1, inner_zero_right, map_zero]

end Profile
end Lemniscate
