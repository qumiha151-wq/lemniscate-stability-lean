import Lemniscate.PeriodicHouseholder

/-! Combining the exact neutral and Householder changes. The common phase
leaves the neutral transform unchanged. The actual transformed differential
expression has zero anchor row and column, hence so does its symmetric pairing. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_neutral_transform_common_phase (e : circleH4Domain T) (ψ f : CircleL2 T) :
    neutralTransform ((-I) • e) ((-I) • ψ) f = neutralTransform e ψ f := by
  rw [neutral_transform_apply, neutral_transform_apply]
  change f+inner ℂ ((-I) • ψ-(-I) • (e : CircleL2 T)) f • ((-I) • (e : CircleL2 T)) = _
  rw [← smul_sub, inner_smul_left, smul_smul]
  simp only [map_neg, Complex.conj_I, neg_neg]
  have hcoef (c : ℂ) : (I*c)*(-I) = c := by
    ring_nf
    simp [Complex.I_sq]
  rw [hcoef]

theorem circle_neutral_inverse_common_phase (e : circleH4Domain T) (ψ f : CircleL2 T) :
    neutralTransformInv ((-I) • e) ((-I) • ψ) f = neutralTransformInv e ψ f := by
  rw [neutral_transform_inv_apply, neutral_transform_inv_apply]
  change f-inner ℂ ((-I) • ψ-(-I) • (e : CircleL2 T)) f • ((-I) • (e : CircleL2 T)) = _
  rw [← smul_sub, inner_smul_left, smul_smul]
  simp only [map_neg, Complex.conj_I, neg_neg]
  have hcoef (c : ℂ) : (I*c)*(-I) = c := by
    ring_nf
    simp [Complex.I_sq]
  rw [hcoef]

noncomputable def circleCenteredOperator (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (ψ : CircleL2 T) (f : circleH4Domain T) : CircleL2 T :=
  circleRotationHouseholder T q p
    (neutralTransform (circleUnitRotationH4 T q p hq hp) ψ
      (circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
        (neutralTransformInvDomain (circleUnitRotationH4 T q p hq hp) ψ
          (circleRotationHouseholderH4 T q p hq hp f))))

noncomputable def circleCenteredSymmetricPairing (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (ψ : CircleL2 T) (f g : circleH4Domain T) : ℂ :=
  (1/2:ℂ)*(inner ℂ (f : CircleL2 T) (circleCenteredOperator T q p hq hp ψ g)+
    inner ℂ (circleCenteredOperator T q p hq hp ψ f) (g : CircleL2 T))

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
theorem paper_householder_h4_anchor :
    circleRotationHouseholderH4 T q p hq hp (circleHouseholderAnchorH4 T) =
      I • circleUnitRotationH4 T q p hq hp := by
  apply Subtype.ext
  rw [circle_rotation_householder_h4_coe, circle_householder_anchor_h4_coe,
    paper_householder_anchor T q p hq hp he hqreal hpreal hs hc ho hr]
  change -((-I) • circleUnitRotation T q p) = I • circleUnitRotation T q p
  rw [neg_smul, neg_neg]

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_centered_operator_zero_column (ψ : CircleL2 T)
    (hd : HasCircleNeutralDecomposition T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circleUnitRotationH4 T q p hq hp) ψ) :
    circleCenteredOperator T q p hq hp ψ (circleHouseholderAnchorH4 T) = 0 := by
  have hk : circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circleUnitRotationH4 T q p hq hp) = 0 := by
    rw [circleUnitRotationH4, map_smul, circle_rotation_h4_kernel T q p hq hp he, smul_zero]
  rw [circleCenteredOperator, hd.2.2.1,
    paper_householder_h4_anchor T q p hq hp he hqreal hpreal hs hc ho hr,
    map_smul, hk, smul_zero, inner_zero_right, zero_smul, sub_zero, map_zero]

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_centered_operator_zero_row (ψ : CircleL2 T)
    (hd : HasCircleNeutralDecomposition T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circleUnitRotationH4 T q p hq hp) ψ) (f : circleH4Domain T) :
    inner ℂ (circleHouseholderAnchor T) (circleCenteredOperator T q p hq hp ψ f) = 0 := by
  have hz := hd.2.2.2.1 (circleRotationHouseholderH4 T q p hq hp f)
  change inner ℂ (circleUnitRotation T q p) _ = 0 at hz
  rw [circleCenteredOperator,
    ← paper_householder_selfadjoint T q p hq hp he hqreal hpreal hs hc ho hr,
    paper_householder_anchor T q p hq hp he hqreal hpreal hs hc ho hr,
    inner_neg_left, inner_smul_left, hz, mul_zero, neg_zero]

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_centered_symmetric_pairing_zero (ψ : CircleL2 T)
    (hd : HasCircleNeutralDecomposition T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circleUnitRotationH4 T q p hq hp) ψ) (f : circleH4Domain T) :
    circleCenteredSymmetricPairing T q p hq hp ψ (circleHouseholderAnchorH4 T) f = 0 ∧
      circleCenteredSymmetricPairing T q p hq hp ψ f (circleHouseholderAnchorH4 T) = 0 := by
  have hc₀ := paper_centered_operator_zero_column T q p hq hp he hqreal hpreal hs hc ho hr ψ hd
  have hr₀ := paper_centered_operator_zero_row T q p hq hp he hqreal hpreal hs hc ho hr ψ hd f
  have hrev : inner ℂ (circleCenteredOperator T q p hq hp ψ f) (circleHouseholderAnchor T) = 0 := by
    rw [← inner_conj_symm, hr₀, map_zero]
  constructor <;> simp only [circleCenteredSymmetricPairing, circle_householder_anchor_h4_coe,
    hc₀, hr₀, hrev, inner_zero_left, inner_zero_right, zero_add, add_zero, mul_zero]

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_exact_centered_neutral_exists :
    ∃ ψ : circleH4Domain T,
      inner ℂ (ψ : CircleL2 T) (circleUnitRotation T q p) = 1 ∧
      circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0 ∧
      circleCenteredOperator T q p hq hp (ψ : CircleL2 T) (circleHouseholderAnchorH4 T) = 0 ∧
      ∀ f : circleH4Domain T,
        circleCenteredSymmetricPairing T q p hq hp (ψ : CircleL2 T) (circleHouseholderAnchorH4 T) f = 0 ∧
        circleCenteredSymmetricPairing T q p hq hp (ψ : CircleL2 T) f (circleHouseholderAnchorH4 T) = 0 := by
  obtain ⟨ψ, hnorm, hzero, _, _, hd⟩ :=
    paper_single_period_neutral_decomposition T q p hq hp he hqreal hpreal hs hc ho hr
  exact ⟨ψ, hnorm, hzero,
    paper_centered_operator_zero_column T q p hq hp he hqreal hpreal hs hc ho hr _ hd,
    paper_centered_symmetric_pairing_zero T q p hq hp he hqreal hpreal hs hc ho hr _ hd⟩

end Profile
end Lemniscate
