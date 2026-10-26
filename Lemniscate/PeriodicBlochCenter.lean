import Lemniscate.PeriodicBlochParity
import Lemniscate.PeriodicCenteredNeutral

/-! Exact center coefficients obtained directly from kernel/adjoint pairings.
Odd coefficients vanish by reflection. No explicit basis-change matrix or
separate maximal-domain theorem for a symmetric operator is used. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_even_sine_sector_reflect (ψ : CircleL2 T) (hψ : InCircleEvenSineSector T ψ) :
    circleReflect T ψ = -ψ := by
  apply circle_fourier_ext T
  intro n
  have hn : fourierCoeff (-ψ) n = -fourierCoeff ψ n := by
    simpa only [neg_one_smul, neg_one_mul] using circle_fourierCoeff_smul T (-1) ψ n
  rw [circle_reflect_fourier, hn, hψ.1]

theorem circle_bloch_odd_pairing_zero (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (e : circleH4Domain T) (ψ : CircleL2 T)
    (he : circleReflectH4 T e = -e) (hψ : circleReflect T ψ = -ψ)
    (j : Fin 5) (hj : Odd (j:ℕ)) : inner ℂ ψ (circleBlochCoefficient T h h₁ h₂ j e) = 0 := by
  have hpar := circle_bloch_coefficient_reflect T h h₁ h₂ hh hh₁ hs j e
  rw [he, map_neg, hj.neg_one_pow, neg_one_smul] at hpar
  have hv : circleReflect T (circleBlochCoefficient T h h₁ h₂ j e) =
      circleBlochCoefficient T h h₁ h₂ j e := (neg_injective hpar).symm
  have hz := circle_reflection_orthogonal T _ ψ hv hψ
  rw [← inner_conj_symm, hz, map_zero]

noncomputable def circleCenteredBlochCoefficient (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (ψ : CircleL2 T) (j : Fin 5) (f : circleH4Domain T) : CircleL2 T :=
  circleRotationHouseholder T q p
    (neutralTransform (circleUnitRotationH4 T q p hq hp) ψ
      (circleBlochCoefficient T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) j
        (neutralTransformInvDomain (circleUnitRotationH4 T q p hq hp) ψ
          (circleRotationHouseholderH4 T q p hq hp f))))

theorem circle_centered_bloch_zero (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (ψ : CircleL2 T) (f : circleH4Domain T) :
    circleCenteredBlochCoefficient T q p hq hp ψ 0 f =
      circleCenteredOperator T q p hq hp ψ f := rfl

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
theorem paper_centered_bloch_anchor_pairing (ψ : CircleL2 T)
    (hnorm : inner ℂ ψ (circleUnitRotation T q p) = 1) (j : Fin 5) :
    inner ℂ (circleHouseholderAnchor T)
      (circleCenteredBlochCoefficient T q p hq hp ψ j (circleHouseholderAnchorH4 T)) =
      inner ℂ ψ (circleBlochCoefficient T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) j
        (circleUnitRotationH4 T q p hq hp)) := by
  let e := circleUnitRotationH4 T q p hq hp
  let N := paperSinglePeriodNeutralOperator T q p hq hp he hqreal hpreal hs hc ho hr
  have hu : inner ℂ (e : CircleL2 T) (e : CircleL2 T) = 1 := N.inner_neutral_self
  have hz : inner ℂ (ψ-(e : CircleL2 T)) (e : CircleL2 T) = 0 :=
    neutral_remainder_pairing e ψ hu hnorm
  have hi : neutralTransformInvDomain e ψ
      (circleRotationHouseholderH4 T q p hq hp (circleHouseholderAnchorH4 T)) = I • e := by
    rw [paper_householder_h4_anchor T q p hq hp he hqreal hpreal hs hc ho hr]
    change I • e-inner ℂ (ψ-(e : CircleL2 T)) (I • (e : CircleL2 T)) • e = I • e
    rw [inner_smul_right, hz, mul_zero, zero_smul, sub_zero]
  change inner ℂ (circleHouseholderAnchor T) (circleRotationHouseholder T q p
    (neutralTransform e ψ (circleBlochCoefficient T (q^2) ((2:ℂ) • (q*p))
      (1-(3:ℂ) • (q^4)) j (neutralTransformInvDomain e ψ
        (circleRotationHouseholderH4 T q p hq hp (circleHouseholderAnchorH4 T)))))) = _
  rw [hi, ← paper_householder_selfadjoint T q p hq hp he hqreal hpreal hs hc ho hr,
    paper_householder_anchor T q p hq hp he hqreal hpreal hs hc ho hr,
    inner_neg_left, inner_smul_left, map_smul, map_smul, inner_smul_right]
  change -(conj (-I)*(I*inner ℂ (e : CircleL2 T)
    (neutralTransform e ψ (circleBlochCoefficient T (q^2) ((2:ℂ) • (q*p))
      (1-(3:ℂ) • (q^4)) j e)))) = _
  rw [neutral_transform_pairing e ψ hu]
  simp only [map_neg, Complex.conj_I, neg_neg]
  ring_nf
  simp [Complex.I_sq]
  rfl

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_centered_bloch_odd_anchor_zero (ψ : CircleL2 T)
    (hnorm : inner ℂ ψ (circleUnitRotation T q p) = 1)
    (hsector : InCircleEvenSineSector T ψ) (j : Fin 5) (hj : Odd (j:ℕ)) :
    inner ℂ (circleHouseholderAnchor T)
      (circleCenteredBlochCoefficient T q p hq hp ψ j (circleHouseholderAnchorH4 T)) = 0 := by
  rw [paper_centered_bloch_anchor_pairing T q p hq hp he hqreal hpreal hs hc ho hr ψ hnorm]
  apply circle_bloch_odd_pairing_zero T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
    (circle_profile_square_deriv T q p hq) (circle_profile_square_second T q p hq hp he) hs
    (circleUnitRotationH4 T q p hq hp) ψ _ (circle_even_sine_sector_reflect T ψ hsector) j hj
  apply Subtype.ext
  rw [circle_reflect_h4_coe, circle_unit_rotation_h4_coe]
  exact circle_unit_rotation_reflect T q p hq hs

end Profile
end Lemniscate
