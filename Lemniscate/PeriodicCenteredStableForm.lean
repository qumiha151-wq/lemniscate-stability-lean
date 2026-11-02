import Lemniscate.PeriodicBlochCenter
import Lemniscate.PeriodicFiniteProjectionL2

/-! Identify the exact constant coefficient on the stable subspace with
the Householder pullback of S0, before any approximation is made. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

set_option maxHeartbeats 1000000 in
theorem paper_centered_zero_stable_form (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = thetaParameter)
    (ψ : CircleL2 T)
    (hd : HasCircleNeutralDecomposition T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circleUnitRotationH4 T q p hq hp) ψ)
    (f g : circleH4Domain T)
    (hf : inner ℂ (circleHouseholderAnchor T) (f:CircleL2 T) = 0)
    (hg : inner ℂ (circleHouseholderAnchor T) (g:CircleL2 T) = 0) :
    (1/2:ℂ)*(inner ℂ (f:CircleL2 T) (circleCenteredBlochCoefficient T q p hq hp ψ 0 g)+
      inner ℂ (circleCenteredBlochCoefficient T q p hq hp ψ 0 f) (g:CircleL2 T)) =
    inner ℂ (circleRotationHouseholderH4 T q p hq hp f:CircleL2 T)
      (circleH4SymmetricOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
        (circleRotationHouseholderH4 T q p hq hp g)) := by
  let U := circleRotationHouseholderH4 T q p hq hp
  let A := circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
  have horth (v : circleH4Domain T) (hv : inner ℂ (circleHouseholderAnchor T) (v:CircleL2 T) = 0) :
      inner ℂ (circleUnitRotation T q p) (U v:CircleL2 T) = 0 := by
    have h := paper_householder_inner T q p hq hp he hqreal hpreal hs hc ho hr
      (circleHouseholderAnchor T) (v:CircleL2 T)
    rw [paper_householder_anchor T q p hq hp he hqreal hpreal hs hc ho hr,hv] at h
    simp only [neg_smul,neg_neg,inner_smul_left,Complex.conj_I] at h
    dsimp only [U]
    rw [circle_rotation_householder_h4_coe]
    exact (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)
  have hpair (v w : circleH4Domain T)
      (hv : inner ℂ (circleHouseholderAnchor T) (v:CircleL2 T) = 0) :
      inner ℂ (v:CircleL2 T) (circleCenteredBlochCoefficient T q p hq hp ψ 0 w) =
        inner ℂ (U v:CircleL2 T) (A (U w)) := by
    rw [circle_centered_bloch_zero,circleCenteredOperator,hd.2.2.1,
      ← paper_householder_selfadjoint T q p hq hp he hqreal hpreal hs hc ho hr]
    rw [← circle_rotation_householder_h4_coe T q p hq hp v]
    simp only [circle_unit_rotation_h4_coe]
    change inner ℂ (U v:CircleL2 T) (A (U w)-
      inner ℂ (circleUnitRotation T q p) (A (U w)) • circleUnitRotation T q p) = _
    rw [inner_sub_right,inner_smul_right,inner_eq_zero_symm.mpr (horth v hv),mul_zero,sub_zero]
  have hpairrev : inner ℂ (circleCenteredBlochCoefficient T q p hq hp ψ 0 f) (g:CircleL2 T) =
      inner ℂ (A (U f)) (U g:CircleL2 T) := by
    simpa only [inner_conj_symm] using congrArg conj (hpair g f hg)
  rw [hpair f g hf,hpairrev]
  have hreal : ∀ x, conj ((q^2 : C(AddCircle T, ℂ)) x) = (q^2 : C(AddCircle T, ℂ)) x := by
    intro x; change conj ((q x)^2) = (q x)^2; simp only [map_pow,hqreal]
  have h₁real : ∀ x, conj (((2:ℂ) • (q*p)) x) = ((2:ℂ) • (q*p)) x := by
    intro x; change conj (2*(q x*p x)) = 2*(q x*p x); simp only [map_mul,map_ofNat,hqreal,hpreal]
  have h₂real : ∀ x, conj ((1-(3:ℂ) • (q^4) : C(AddCircle T, ℂ)) x) =
      (1-(3:ℂ) • (q^4) : C(AddCircle T, ℂ)) x := by
    intro x; change conj (1-3*(q x)^4) = 1-3*(q x)^4
    simp only [map_sub,map_mul,map_one,map_ofNat,map_pow,hqreal]
  rw [circle_h4_formal_adjoint_green T _ _ _ (circle_profile_square_deriv T q p hq)
    (circle_profile_square_second T q p hq hp he) hreal h₁real h₂real (U f) (U g),
    circle_h4_formal_adjoint_split T _ _ _ (U g),circle_h4_operator_apply]
  unfold circleLinearL2Expression
  rw [← circle_h4_symmetric_operator_apply T _ _ _ (U g)]
  simp only [inner_add_right,inner_sub_right]
  ring

end Lemniscate
