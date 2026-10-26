import Lemniscate.PeriodicBlochCenter

/-! The exact transformed Bloch polynomial and cancellation of the neutral
quadratic factor. The identities hold on the actual H4 domain and use exact
neutral data; division by the parameter is performed only after cancellation. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleCenteredBlochOperator (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (ψ : CircleL2 T) (α : ℝ) (f : circleH4Domain T) : CircleL2 T :=
  circleRotationHouseholder T q p
    (neutralTransform (circleUnitRotationH4 T q p hq hp) ψ
      (circleBlochOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) α
        (neutralTransformInvDomain (circleUnitRotationH4 T q p hq hp) ψ
          (circleRotationHouseholderH4 T q p hq hp f))))

theorem circle_centered_bloch_polynomial (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (ψ : CircleL2 T) (α : ℝ) (f : circleH4Domain T) :
    circleCenteredBlochOperator T q p hq hp ψ α f =
      circleCenteredBlochCoefficient T q p hq hp ψ 0 f+
      (α:ℂ) • circleCenteredBlochCoefficient T q p hq hp ψ 1 f+
      (α:ℂ)^2 • circleCenteredBlochCoefficient T q p hq hp ψ 2 f+
      (α:ℂ)^3 • circleCenteredBlochCoefficient T q p hq hp ψ 3 f+
      (α:ℂ)^4 • circleCenteredBlochCoefficient T q p hq hp ψ 4 f := by
  rw [circleCenteredBlochOperator, circle_bloch_polynomial]
  simp only [map_add, map_smul]
  rfl

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
theorem paper_centered_bloch_top (ψ : CircleL2 T)
    (hd : HasCircleNeutralDecomposition T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circleUnitRotationH4 T q p hq hp) ψ) (f : circleH4Domain T) :
    circleCenteredBlochCoefficient T q p hq hp ψ 4 f =
      ((-4*thetaParameter^2 : ℝ) : ℂ) • (f : CircleL2 T) := by
  have hright (g : CircleL2 T) := (hd.1 g).1
  rw [circleCenteredBlochCoefficient,
    circle_bloch_top_coefficient T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) thetaParameter hr,
    map_smul, map_smul, neutral_transform_inv_domain_coe, hright,
    circle_rotation_householder_h4_coe,
    paper_householder_involutive T q p hq hp he hqreal hpreal hs hc ho hr]

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_centered_bloch_center_polynomial (ψ : CircleL2 T)
    (hnorm : inner ℂ ψ (circleUnitRotation T q p) = 1)
    (hsector : InCircleEvenSineSector T ψ)
    (hd : HasCircleNeutralDecomposition T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circleUnitRotationH4 T q p hq hp) ψ) (α : ℝ) :
    inner ℂ (circleHouseholderAnchor T)
      (circleCenteredBlochOperator T q p hq hp ψ α (circleHouseholderAnchorH4 T)) =
      (α:ℂ)^2 * inner ℂ (circleHouseholderAnchor T)
        (circleCenteredBlochCoefficient T q p hq hp ψ 2 (circleHouseholderAnchorH4 T))-
      4*(thetaParameter:ℂ)^2*(α:ℂ)^4 := by
  have h0 := paper_centered_operator_zero_column T q p hq hp he hqreal hpreal hs hc ho hr ψ hd
  have h1 := paper_centered_bloch_odd_anchor_zero T q p hq hp he hqreal hpreal hs hc ho hr
    ψ hnorm hsector 1 (by decide)
  have h3 := paper_centered_bloch_odd_anchor_zero T q p hq hp he hqreal hpreal hs hc ho hr
    ψ hnorm hsector 3 (by decide)
  rw [circle_centered_bloch_polynomial]
  simp only [inner_add_right, inner_smul_right, circle_centered_bloch_zero, h0,
    inner_zero_right, h1, h3, paper_centered_bloch_top T q p hq hp he hqreal hpreal hs hc ho hr ψ hd,
    circle_householder_anchor_h4_coe, inner_smul_right, circle_householder_anchor_unit]
  push_cast
  ring

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_centered_bloch_center_scaled (ψ : CircleL2 T)
    (hnorm : inner ℂ ψ (circleUnitRotation T q p) = 1)
    (hsector : InCircleEvenSineSector T ψ)
    (hd : HasCircleNeutralDecomposition T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circleUnitRotationH4 T q p hq hp) ψ) (α : ℝ) (hα : α ≠ 0) :
    ((α:ℂ)⁻¹)^2 * inner ℂ (circleHouseholderAnchor T)
      (circleCenteredBlochOperator T q p hq hp ψ α (circleHouseholderAnchorH4 T)) =
      inner ℂ (circleHouseholderAnchor T)
        (circleCenteredBlochCoefficient T q p hq hp ψ 2 (circleHouseholderAnchorH4 T))-
      4*(thetaParameter:ℂ)^2*(α:ℂ)^2 := by
  rw [paper_centered_bloch_center_polynomial T q p hq hp he hqreal hpreal hs hc ho hr
    ψ hnorm hsector hd]
  have ha : (α:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα
  field_simp [ha]

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_centered_bloch_cross_row_polynomial (ψ : CircleL2 T)
    (hd : HasCircleNeutralDecomposition T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circleUnitRotationH4 T q p hq hp) ψ) (α : ℝ) (f : circleH4Domain T)
    (hf : inner ℂ (circleHouseholderAnchor T) (f : CircleL2 T) = 0) :
    inner ℂ (circleHouseholderAnchor T) (circleCenteredBlochOperator T q p hq hp ψ α f) =
      (α:ℂ)*inner ℂ (circleHouseholderAnchor T) (circleCenteredBlochCoefficient T q p hq hp ψ 1 f)+
      (α:ℂ)^2*inner ℂ (circleHouseholderAnchor T) (circleCenteredBlochCoefficient T q p hq hp ψ 2 f)+
      (α:ℂ)^3*inner ℂ (circleHouseholderAnchor T) (circleCenteredBlochCoefficient T q p hq hp ψ 3 f) := by
  have h0 := paper_centered_operator_zero_row T q p hq hp he hqreal hpreal hs hc ho hr ψ hd f
  rw [circle_centered_bloch_polynomial]
  simp only [inner_add_right, inner_smul_right, circle_centered_bloch_zero, h0,
    paper_centered_bloch_top T q p hq hp he hqreal hpreal hs hc ho hr ψ hd,
    inner_smul_right, hf, mul_zero, zero_add, add_zero]

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_centered_bloch_cross_column_polynomial (ψ : CircleL2 T)
    (hd : HasCircleNeutralDecomposition T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circleUnitRotationH4 T q p hq hp) ψ) (α : ℝ) (f : circleH4Domain T)
    (hf : inner ℂ (circleHouseholderAnchor T) (f : CircleL2 T) = 0) :
    inner ℂ (f : CircleL2 T)
      (circleCenteredBlochOperator T q p hq hp ψ α (circleHouseholderAnchorH4 T)) =
      (α:ℂ)*inner ℂ (f : CircleL2 T)
        (circleCenteredBlochCoefficient T q p hq hp ψ 1 (circleHouseholderAnchorH4 T))+
      (α:ℂ)^2*inner ℂ (f : CircleL2 T)
        (circleCenteredBlochCoefficient T q p hq hp ψ 2 (circleHouseholderAnchorH4 T))+
      (α:ℂ)^3*inner ℂ (f : CircleL2 T)
        (circleCenteredBlochCoefficient T q p hq hp ψ 3 (circleHouseholderAnchorH4 T)) := by
  have h0 := paper_centered_operator_zero_column T q p hq hp he hqreal hpreal hs hc ho hr ψ hd
  have hf' : inner ℂ (f : CircleL2 T) (circleHouseholderAnchor T) = 0 := by
    rw [← inner_conj_symm, hf, map_zero]
  rw [circle_centered_bloch_polynomial]
  simp only [inner_add_right, inner_smul_right, circle_centered_bloch_zero, h0, inner_zero_right,
    paper_centered_bloch_top T q p hq hp he hqreal hpreal hs hc ho hr ψ hd,
    circle_householder_anchor_h4_coe, inner_smul_right, hf', mul_zero, zero_add, add_zero]

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_centered_bloch_cross_row_scaled (ψ : CircleL2 T)
    (hd : HasCircleNeutralDecomposition T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circleUnitRotationH4 T q p hq hp) ψ) (α : ℝ) (hα : α ≠ 0) (f : circleH4Domain T)
    (hf : inner ℂ (circleHouseholderAnchor T) (f : CircleL2 T) = 0) :
    (α:ℂ)⁻¹*inner ℂ (circleHouseholderAnchor T) (circleCenteredBlochOperator T q p hq hp ψ α f) =
      inner ℂ (circleHouseholderAnchor T) (circleCenteredBlochCoefficient T q p hq hp ψ 1 f)+
      (α:ℂ)*inner ℂ (circleHouseholderAnchor T) (circleCenteredBlochCoefficient T q p hq hp ψ 2 f)+
      (α:ℂ)^2*inner ℂ (circleHouseholderAnchor T) (circleCenteredBlochCoefficient T q p hq hp ψ 3 f) := by
  rw [paper_centered_bloch_cross_row_polynomial T q p hq hp he hqreal hpreal hs hc ho hr ψ hd α f hf]
  have ha : (α:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα
  field_simp [ha]

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_centered_bloch_cross_column_scaled (ψ : CircleL2 T)
    (hd : HasCircleNeutralDecomposition T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circleUnitRotationH4 T q p hq hp) ψ) (α : ℝ) (hα : α ≠ 0) (f : circleH4Domain T)
    (hf : inner ℂ (circleHouseholderAnchor T) (f : CircleL2 T) = 0) :
    (α:ℂ)⁻¹*inner ℂ (f : CircleL2 T)
      (circleCenteredBlochOperator T q p hq hp ψ α (circleHouseholderAnchorH4 T)) =
      inner ℂ (f : CircleL2 T)
        (circleCenteredBlochCoefficient T q p hq hp ψ 1 (circleHouseholderAnchorH4 T))+
      (α:ℂ)*inner ℂ (f : CircleL2 T)
        (circleCenteredBlochCoefficient T q p hq hp ψ 2 (circleHouseholderAnchorH4 T))+
      (α:ℂ)^2*inner ℂ (f : CircleL2 T)
        (circleCenteredBlochCoefficient T q p hq hp ψ 3 (circleHouseholderAnchorH4 T)) := by
  rw [paper_centered_bloch_cross_column_polynomial T q p hq hp he hqreal hpreal hs hc ho hr ψ hd α f hf]
  have ha : (α:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα
  field_simp [ha]

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_exact_bloch_center_cancellation_exists :
    ∃ ψ : circleH4Domain T,
      inner ℂ (ψ : CircleL2 T) (circleUnitRotation T q p) = 1 ∧
      circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0 ∧
      ∀ α : ℝ, α ≠ 0 →
        ((α:ℂ)⁻¹)^2*inner ℂ (circleHouseholderAnchor T)
          (circleCenteredBlochOperator T q p hq hp (ψ : CircleL2 T) α (circleHouseholderAnchorH4 T)) =
        inner ℂ (circleHouseholderAnchor T)
          (circleCenteredBlochCoefficient T q p hq hp (ψ : CircleL2 T) 2 (circleHouseholderAnchorH4 T))-
        4*(thetaParameter:ℂ)^2*(α:ℂ)^2 := by
  obtain ⟨ψ, hnorm, hzero, _, hsector, hd⟩ :=
    paper_single_period_neutral_decomposition T q p hq hp he hqreal hpreal hs hc ho hr
  exact ⟨ψ, hnorm, hzero,
    paper_centered_bloch_center_scaled T q p hq hp he hqreal hpreal hs hc ho hr _ hnorm hsector hd⟩

end Profile
end Lemniscate
