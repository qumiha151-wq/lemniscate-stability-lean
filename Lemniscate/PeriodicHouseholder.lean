import Lemniscate.NeutralHouseholder
import Lemniscate.PeriodicHouseholderAnchor

/-! The actual Householder operator for the paper's phased rotation vector.
The denominator is proved greater than one from the first Fourier coefficient;
no extra invertibility or phase-sign assumption is introduced. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleRotationHouseholder (q p : C(AddCircle T, ℂ)) :
    CircleL2 T →L[ℂ] CircleL2 T :=
  neutralHouseholder ((-I) • circleUnitRotation T q p) (circleHouseholderAnchor T)

noncomputable def circleRotationHouseholderH4 (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (f : circleH4Domain T) : circleH4Domain T :=
  neutralHouseholderDomain ((-I) • circleUnitRotationH4 T q p hq hp) (circleHouseholderAnchorH4 T) f

theorem circle_rotation_householder_h4_coe (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3))) (f : circleH4Domain T) :
    (circleRotationHouseholderH4 T q p hq hp f : CircleL2 T) =
      circleRotationHouseholder T q p (f : CircleL2 T) := by
  exact neutral_householder_domain_coe _ _ f

theorem circle_rotation_householder_no_odd (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p)
    (ho : ∀ i : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*i+1) = 0)
    (f : CircleL2 T) (hf : ∀ i : ℤ, fourierCoeff f (2*i+1) = 0) (i : ℤ) :
    fourierCoeff (circleRotationHouseholder T q p f) (2*i+1) = 0 := by
  simp only [circleRotationHouseholder, neutral_householder_apply, circle_fourierCoeff_sub,
    circle_fourierCoeff_smul, circle_fourierCoeff_add, hf,
    circle_unit_rotation_no_odd T q p hq ho, circle_householder_anchor_no_odd,
    mul_zero, zero_add, sub_zero]

theorem circle_rotation_householder_reflect (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n) (f : CircleL2 T) :
    circleRotationHouseholder T q p (circleReflect T f) =
      circleReflect T (circleRotationHouseholder T q p f) := by
  let u := (-I) • circleUnitRotation T q p+circleHouseholderAnchor T
  have hu : circleReflect T u = -u := by
    dsimp [u]
    rw [circle_reflect_add, circle_reflect_smul, circle_unit_rotation_reflect T q p hq hs,
      circle_householder_anchor_reflect, smul_neg, ← neg_add]
  have hi : inner ℂ u (circleReflect T f) = -inner ℂ u f := by
    rw [← circle_reflect_selfadjoint, hu, inner_neg_left]
  simp only [circleRotationHouseholder, neutral_householder_apply]
  change circleReflect T f-((1+inner ℂ ((-I) • circleUnitRotation T q p)
    (circleHouseholderAnchor T))⁻¹*inner ℂ u (circleReflect T f)) • u =
      circleReflect T (f-((1+inner ℂ ((-I) • circleUnitRotation T q p)
        (circleHouseholderAnchor T))⁻¹*inner ℂ u f) • u)
  rw [hi, circle_reflect_sub, circle_reflect_smul, hu, mul_neg, neg_smul, smul_neg]

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
theorem paper_rotation_householder_hypotheses :
    inner ℂ ((-I) • circleUnitRotation T q p) ((-I) • circleUnitRotation T q p) = 1 ∧
    inner ℂ (circleHouseholderAnchor T) ((-I) • circleUnitRotation T q p) =
      inner ℂ ((-I) • circleUnitRotation T q p) (circleHouseholderAnchor T) ∧
    1 < (1+inner ℂ ((-I) • circleUnitRotation T q p) (circleHouseholderAnchor T)).re ∧
    1+inner ℂ ((-I) • circleUnitRotation T q p) (circleHouseholderAnchor T) ≠ 0 := by
  let N := paperSinglePeriodNeutralOperator T q p hq hp he hqreal hpreal hs hc ho hr
  obtain ⟨c, hcpos, hleft, hright⟩ := circle_unit_rotation_phase_anchor T q p hq hs hc ho
  have hd : 1 < (1+inner ℂ ((-I) • circleUnitRotation T q p) (circleHouseholderAnchor T)).re := by
    rw [hright, Complex.add_re, Complex.one_re, Complex.ofReal_re]
    linarith
  refine ⟨?_, hleft.trans hright.symm, hd, ?_⟩
  · rw [circle_common_phase_inner]
    exact N.inner_neutral_self
  · intro hz
    rw [hz, Complex.zero_re] at hd
    norm_num at hd

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_householder_involutive (f : CircleL2 T) :
    circleRotationHouseholder T q p (circleRotationHouseholder T q p f) = f := by
  obtain ⟨hu, hsym, _, hd⟩ :=
    paper_rotation_householder_hypotheses T q p hq hp he hqreal hpreal hs hc ho hr
  exact neutral_householder_involutive _ _ hu (circle_householder_anchor_unit T) hsym hd f

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_householder_selfadjoint (f g : CircleL2 T) :
    inner ℂ (circleRotationHouseholder T q p f) g =
      inner ℂ f (circleRotationHouseholder T q p g) := by
  obtain ⟨_, hsym, _, _⟩ :=
    paper_rotation_householder_hypotheses T q p hq hp he hqreal hpreal hs hc ho hr
  exact neutral_householder_selfadjoint _ _ hsym f g

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_householder_anchor :
    circleRotationHouseholder T q p (circleHouseholderAnchor T) =
      -((-I) • circleUnitRotation T q p) := by
  obtain ⟨_, _, _, hd⟩ :=
    paper_rotation_householder_hypotheses T q p hq hp he hqreal hpreal hs hc ho hr
  exact neutral_householder_anchor _ _ (circle_householder_anchor_unit T) hd

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_householder_inner (f g : CircleL2 T) :
    inner ℂ (circleRotationHouseholder T q p f) (circleRotationHouseholder T q p g) =
      inner ℂ f g := by
  obtain ⟨hu, hsym, _, hd⟩ :=
    paper_rotation_householder_hypotheses T q p hq hp he hqreal hpreal hs hc ho hr
  exact neutral_householder_inner _ _ hu (circle_householder_anchor_unit T) hsym hd f g

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_householder_norm (f : CircleL2 T) :
    ‖circleRotationHouseholder T q p f‖ = ‖f‖ := by
  obtain ⟨hu, hsym, _, hd⟩ :=
    paper_rotation_householder_hypotheses T q p hq hp he hqreal hpreal hs hc ho hr
  exact neutral_householder_norm _ _ hu (circle_householder_anchor_unit T) hsym hd f

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_householder_h4_involutive (f : circleH4Domain T) :
    circleRotationHouseholderH4 T q p hq hp (circleRotationHouseholderH4 T q p hq hp f) = f := by
  apply Subtype.ext
  rw [circle_rotation_householder_h4_coe, circle_rotation_householder_h4_coe]
  exact paper_householder_involutive T q p hq hp he hqreal hpreal hs hc ho hr (f : CircleL2 T)

end Profile
end Lemniscate
