import Lemniscate.PeriodicExactChangeBounds
import Lemniscate.PeriodicFormComparison
import Lemniscate.PeriodicBlochCoefficientBounds
import Lemniscate.PeriodicBlochCenter

/-! A small form error for the actual positive-degree centered Bloch
coefficients. The common phase and both changes of variables are explicit. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

theorem circle_neutral_inverse_domain_common_phase (e : circleH4Domain T)
    (ψ : CircleL2 T) (f : circleH4Domain T) :
    neutralTransformInvDomain ((-I) • e) ((-I) • ψ) f = neutralTransformInvDomain e ψ f := by
  apply Subtype.ext
  rw [neutral_transform_inv_domain_coe,neutral_transform_inv_domain_coe,
    circle_neutral_inverse_common_phase]

private theorem transformed_pairing_green (e a ψ f : circleH4Domain T)
    (hea : inner ℂ (a:CircleL2 T) (e:CircleL2 T) = inner ℂ (e:CircleL2 T) (a:CircleL2 T))
    (v : CircleL2 T) :
    inner ℂ (f:CircleL2 T)
      (neutralHouseholder (e:CircleL2 T) (a:CircleL2 T) (neutralTransform e (ψ:CircleL2 T) v)) =
    inner ℂ (neutralTransformAdjointDomain e ψ (neutralHouseholderDomain e a f):CircleL2 T) v := by
  rw [← neutral_householder_selfadjoint (e:CircleL2 T) (a:CircleL2 T) hea,
    ← neutral_householder_domain_coe]
  exact (neutral_transform_adjoint_domain_green e ψ (neutralHouseholderDomain e a f) v).symm

set_option maxHeartbeats 1000000 in
theorem paper_centered_positive_coefficient_difference (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = thetaParameter)
    (ψ : circleH4Domain T)
    (hψnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p) = 1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (hh : ‖q^2‖ ≤ 1) (hh₁ : ‖(2:ℂ) • (q*p)‖ ≤ 2)
    (hh₂ : ‖1-(3:ℂ) • (q^4)‖ ≤ 4) (hκ : 2*Real.pi/T ≤ 1)
    (j : Fin 5) (hj : j ≠ 0) (f g : circleH4Domain T) :
    ‖(1/2:ℂ)*(inner ℂ (f:CircleL2 T) (circleCenteredBlochCoefficient T q p hq hp (ψ:CircleL2 T) j g)+
      inner ℂ (circleCenteredBlochCoefficient T q p hq hp (ψ:CircleL2 T) j f) (g:CircleL2 T))-
      circleFiniteSymmetricCoefficient T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) j f g‖
        ≤ (1/2000:ℝ)*‖f‖*‖g‖ := by
  let e := (-I) • circleUnitRotationH4 T q p hq hp
  let φ := (-I) • ψ
  let a := circleHouseholderAnchorH4 T
  let eN := circleFiniteRotationPhase T
  let φN := circleFiniteAdjointPhaseH4 T
  let L := circleExactLeftInput T q p hq hp ψ
  let R := circleExactRightInput T q p hq hp ψ
  let LN (v : circleH4Domain T) := neutralTransformAdjointDomain eN φN (neutralHouseholderDomain eN a v)
  let RN := circleFiniteRightInput T
  let A := circleBlochCoefficient T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) j
  let Astar := circleBlochAdjointCoefficient T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) j
  have hb (v : circleH4Domain T) := paper_neutral_input_difference_bounds T q p hq hp he
    hqreal hpreal hs hc ho hr ψ hψnorm hψzero v
  have hL (v : circleH4Domain T) : circleAngularH4Norm T (L v-LN v) ≤ 5000*(1/10^11:ℝ)*‖v‖ :=
    (hb v).1
  have hR (v : circleH4Domain T) : circleAngularH4Norm T (R v-RN v) ≤ 5000*(1/10^11:ℝ)*‖v‖ :=
    (hb v).2.1
  have hLN (v : circleH4Domain T) : ‖LN v‖ ≤ 2*‖v‖ := (hb v).2.2.2.1
  have hR0 (v : circleH4Domain T) : ‖R v‖ ≤ 2*‖v‖ := (hb v).2.2.2.2.1
  have hhder := circle_profile_square_deriv T q p hq
  have hh₁der := circle_profile_square_second T q p hq hp he
  have hreal : ∀ x, conj ((q^2 : C(AddCircle T, ℂ)) x) = (q^2 : C(AddCircle T, ℂ)) x := by
    intro x; change conj ((q x)^2) = (q x)^2; simp only [map_pow,hqreal]
  have h₁real : ∀ x, conj (((2:ℂ) • (q*p)) x) = ((2:ℂ) • (q*p)) x := by
    intro x; change conj (2*(q x*p x)) = 2*(q x*p x); simp only [map_mul,map_ofNat,hqreal,hpreal]
  have h₂real : ∀ x, conj ((1-(3:ℂ) • (q^4) : C(AddCircle T, ℂ)) x) =
      (1-(3:ℂ) • (q^4) : C(AddCircle T, ℂ)) x := by
    intro x; change conj (1-3*(q x)^4) = 1-3*(q x)^4
    simp only [map_sub,map_mul,map_one,map_ofNat,map_pow,hqreal]
  have hbounds (v : circleH4Domain T) := circle_bloch_coefficient_angular_bounds T
    (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) hh hh₁ hh₂ hκ v
  have hgreen := circle_bloch_coefficient_green T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
    hhder hh₁der hreal h₁real h₂real j
  have hest := circle_transformed_symmetric_form_difference_bound T A Astar hgreen
    (fun v => (hbounds v).1 j) (fun v => (hbounds v).2.1 j)
    L LN R RN (1/10^11) (by norm_num) hL hR hLN hR0 f g
  have hea : inner ℂ (a:CircleL2 T) (e:CircleL2 T) = inner ℂ (e:CircleL2 T) (a:CircleL2 T) :=
    (paper_rotation_householder_hypotheses T q p hq hp he hqreal hpreal hs hc ho hr).2.1
  have heNa : inner ℂ (a:CircleL2 T) (eN:CircleL2 T) = inner ℂ (eN:CircleL2 T) (a:CircleL2 T) :=
    (circle_finite_householder_hypotheses T).2.1
  have hRphase (v : circleH4Domain T) : R v = neutralTransformInvDomain
      (circleUnitRotationH4 T q p hq hp) (ψ:CircleL2 T) (circleRotationHouseholderH4 T q p hq hp v) := by
    exact circle_neutral_inverse_domain_common_phase T _ _ _
  have hexact (v w : circleH4Domain T) :
      inner ℂ (v:CircleL2 T) (circleCenteredBlochCoefficient T q p hq hp (ψ:CircleL2 T) j w) =
        inner ℂ (L v:CircleL2 T) (A (R w)) := by
    unfold circleCenteredBlochCoefficient
    rw [← hRphase w,← circle_neutral_transform_common_phase T (circleUnitRotationH4 T q p hq hp) (ψ:CircleL2 T)]
    exact transformed_pairing_green T e a φ v hea (A (R w))
  have hfinite (v w : circleH4Domain T) :
      inner ℂ (v:CircleL2 T) (circleFiniteTransformedOperator T A w) =
        inner ℂ (LN v:CircleL2 T) (A (RN w)) := by
    exact transformed_pairing_green T eN a φN v heNa (A (RN w))
  have hexactrev (v w : circleH4Domain T) :
      inner ℂ (circleCenteredBlochCoefficient T q p hq hp (ψ:CircleL2 T) j v) (w:CircleL2 T) =
        inner ℂ (A (R v)) (L w:CircleL2 T) := by
    simpa only [inner_conj_symm] using congrArg conj (hexact w v)
  have hfiniterev (v w : circleH4Domain T) :
      inner ℂ (circleFiniteTransformedOperator T A v) (w:CircleL2 T) =
        inner ℂ (A (RN v)) (LN w:CircleL2 T) := by
    simpa only [inner_conj_symm] using congrArg conj (hfinite w v)
  rw [circleFiniteSymmetricCoefficient,if_neg hj,hexact,hexactrev,hfinite,hfiniterev]
  apply hest.trans
  have hm := mul_nonneg (norm_nonneg f) (norm_nonneg g)
  nlinarith only [hm]

end Lemniscate
