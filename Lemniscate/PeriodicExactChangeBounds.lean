import Lemniscate.PeriodicNeutralInputComparison
import Lemniscate.PeriodicFiniteChangeBounds
import Lemniscate.PeriodicHouseholder

/-! Discharge the vector hypotheses of the comparison estimate for the
paper's actual normalized neutral vectors. The exact and finite phases agree. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleExactLeftInput (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (ψ f : circleH4Domain T) : circleH4Domain T :=
  neutralTransformAdjointDomain ((-I) • circleUnitRotationH4 T q p hq hp) ((-I) • ψ)
    (circleRotationHouseholderH4 T q p hq hp f)

noncomputable def circleExactRightInput (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (ψ f : circleH4Domain T) : circleH4Domain T :=
  neutralTransformInvDomain ((-I) • circleUnitRotationH4 T q p hq hp) (((-I) • ψ):CircleL2 T)
    (circleRotationHouseholderH4 T q p hq hp f)

theorem circle_anchor_angular_h4_norm :
    circleAngularH4Norm T (circleHouseholderAnchorH4 T) = 31 := by
  have hid : circleHouseholderAnchorH4 T = I • circleSineH4 T 0 := by
    have hfactor : I*evenSineFactor = evenCosineFactor := by
      simp [evenSineFactor,← mul_assoc]
    simp only [circleSineH4,smul_smul,hfactor]
    rfl
  rw [hid,circle_angular_h4_norm_smul,Complex.norm_I,one_mul,circle_sine_h4_angular_norm]
  norm_num [Fin.sum_univ_succ]

set_option maxHeartbeats 1000000 in
theorem paper_neutral_input_difference_bounds (q p : C(AddCircle T, ℂ))
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
    (f : circleH4Domain T) :
    let e := (-I) • circleUnitRotationH4 T q p hq hp
    let φ := (-I) • ψ
    let a := circleHouseholderAnchorH4 T
    let U := neutralHouseholderDomain e a f
    let UN := neutralHouseholderDomain (circleFiniteRotationPhase T) a f
    let L := neutralTransformAdjointDomain e φ U
    let LN := neutralTransformAdjointDomain (circleFiniteRotationPhase T) (circleFiniteAdjointPhaseH4 T) UN
    let R := neutralTransformInvDomain e (φ:CircleL2 T) U
    let RN := circleFiniteRightInput T f
    circleAngularH4Norm T (L-LN) ≤ 5000*(1/10^11:ℝ)*‖f‖ ∧
    circleAngularH4Norm T (R-RN) ≤ 5000*(1/10^11:ℝ)*‖f‖ ∧
    ‖L‖ ≤ 2*‖f‖ ∧ ‖LN‖ ≤ 2*‖f‖ ∧ ‖R‖ ≤ 2*‖f‖ ∧ ‖RN‖ ≤ 2*‖f‖ ∧
    circleAngularH4Norm T (U-UN) ≤ 5000*(1/10^11:ℝ)*‖f‖ ∧
    ‖U‖ ≤ 2*‖f‖ ∧ ‖UN‖ ≤ 2*‖f‖ := by
  let e := (-I) • circleUnitRotationH4 T q p hq hp
  let φ := (-I) • ψ
  let eN := circleFiniteRotationPhase T
  let φN := circleFiniteAdjointPhaseH4 T
  let a := circleHouseholderAnchorH4 T
  let ε : ℝ := 1/10^11
  have hε : 0 ≤ ε := by norm_num [ε]
  have hrot := paper_rotation_approximation_bounds T q p hq hp he hqreal hpreal hs hc ho hr
  have hsector := paper_single_period_adjoint_vector_sector T q p hq hp he hqreal hpreal hs hc ho hr
    ψ hψnorm hψzero
  have hnegcoeff (n : ℤ) : fourierCoeff ((-ψ:circleH4Domain T):CircleL2 T) n =
      -fourierCoeff (ψ:CircleL2 T) n := by
    simpa only [neg_one_smul,neg_one_mul,Submodule.coe_neg] using circle_fourierCoeff_smul T (-1) (ψ:CircleL2 T) n
  have hnegsector : InCircleEvenSineSector T ((-ψ:circleH4Domain T):CircleL2 T) := by
    constructor
    · intro n; rw [hnegcoeff,hnegcoeff,hsector.1]
    · intro n; rw [hnegcoeff,hsector.2,neg_zero]
  have hnegnorm : inner ℂ ((-ψ:circleH4Domain T):CircleL2 T) (-circleUnitRotation T q p) = 1 := by
    simpa only [Submodule.coe_neg,inner_neg_left,inner_neg_right,neg_neg] using hψnorm
  have hnegzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) (-ψ) = 0 := by
    rw [map_neg,hψzero,neg_zero]
  have hadj := paper_adjoint_approximation_bounds T q p hq hp he hqreal hpreal hs hc ho hr
    (-ψ) hnegnorm hnegzero hnegsector
  have herid : e-eN = I • (-circleUnitRotationH4 T q p hq hp-circleRotationApproximation T) := by
    simp only [e,eN,circleFiniteRotationPhase,smul_sub,smul_neg,neg_smul]
  have hφid : φ-φN = I • (-ψ-circleAdjointApproximation T) := by
    simp only [φ,φN,circleFiniteAdjointPhaseH4,smul_sub,smul_neg,neg_smul]
  have heδ : circleAngularH4Norm T (e-eN) ≤ ε := by
    rw [herid,circle_angular_h4_norm_smul,Complex.norm_I,one_mul]
    exact hrot.1.le.trans (by norm_num [ε])
  have hφδ : circleAngularH4Norm T (φ-φN) ≤ ε := by
    rw [hφid,circle_angular_h4_norm_smul,Complex.norm_I,one_mul]
    exact hadj.1.le.trans (by norm_num [ε])
  have heNH4 : circleAngularH4Norm T eN ≤ 200 := by
    simpa only [eN,circleFiniteRotationPhase,circle_angular_h4_norm_smul,Complex.norm_I,one_mul] using hrot.2.2.le
  have hφNH4 : circleAngularH4Norm T φN ≤ 200 := by
    simpa only [φN,circleFiniteAdjointPhaseH4,circle_angular_h4_norm_smul,Complex.norm_I,one_mul] using hadj.2.2.le
  have huNH4 : circleAngularH4Norm T (eN+a) ≤ 231 := by
    have h := circle_angular_h4_norm_add_le T eN a
    change circleAngularH4Norm T (eN+a) ≤ circleAngularH4Norm T eN+
      circleAngularH4Norm T (circleHouseholderAnchorH4 T) at h
    rw [circle_anchor_angular_h4_norm] at h
    linarith only [h,heNH4]
  have hchange := circle_finite_change_l2_bounds T
  have ha : ‖a‖ ≤ 1 := by change ‖circleHouseholderAnchor T‖ ≤ 1; rw [hchange.1]
  have heN : ‖eN‖ ≤ 1 := by
    change ‖(circleFiniteRotationPhase T:CircleL2 T)‖ ≤ 1
    rw [(circle_finite_phase_normalization T).1]
  rcases paper_rotation_householder_hypotheses T q p hq hp he hqreal hpreal hs hc ho hr with
    ⟨heunit,hesym,hdre,hd0⟩
  have he0 : ‖e‖ ≤ 1 := by
    have h := congrArg Complex.re heunit
    simp [inner_self_eq_norm_sq_to_K,pow_two] at h
    change ‖(((-I) • circleUnitRotationH4 T q p hq hp):circleH4Domain T)‖ ≤ 1
    change ‖(-I) • circleUnitRotation T q p‖ ≤ 1
    simp only [norm_smul,norm_neg,Complex.norm_I,one_mul] at h ⊢
    nlinarith only [h,norm_nonneg (circleUnitRotation T q p)]
  have hd : 1 ≤ ‖1+inner ℂ (e:CircleL2 T) (a:CircleL2 T)‖ := by
    exact hdre.le.trans (Complex.re_le_norm _)
  have hzN : ‖φN-eN‖ ≤ 1 := hchange.2.1
  have hzNsmall : ‖φN-eN‖ < (1:ℝ)/20 := by
    change ‖((φN-eN:circleH4Domain T):CircleL2 T)‖ < (1:ℝ)/20
    have h := (circle_finite_normalization_bounds T).2.2
    simpa only [φN,eN,circleFiniteAdjointPhaseH4,circleFiniteRotationPhase,← smul_sub,
      Submodule.coe_sub,Submodule.coe_smul_of_tower,norm_smul,Complex.norm_I,one_mul] using h
  have hz : ‖φ-e‖ ≤ 1 := by
    have hid : φ-e = (φN-eN)+((φ-φN)-(e-eN)) := by abel
    have h1 := (circle_norm_le_angular_h4 T _).trans hφδ
    have h2 := (circle_norm_le_angular_h4 T _).trans heδ
    change ‖φ-φN‖ ≤ ε at h1
    change ‖e-eN‖ ≤ ε at h2
    rw [hid]
    have ht := norm_add_le (φN-eN) ((φ-φN)-(e-eN))
    have hs := norm_sub_le (φ-φN) (e-eN)
    calc
      _ ≤ ‖φN-eN‖+‖(φ-φN)-(e-eN)‖ := ht
      _ ≤ 1/20+(ε+ε) := add_le_add hzNsmall.le (hs.trans (add_le_add h1 h2))
      _ ≤ 1 := by norm_num [ε]
  have hU : ‖neutralHouseholderDomain e a f‖ ≤ ‖f‖ := by
    change ‖(neutralHouseholderDomain e a f:CircleL2 T)‖ ≤ ‖(f:CircleL2 T)‖
    rw [neutral_householder_domain_coe]
    exact (paper_householder_norm T q p hq hp he hqreal hpreal hs hc ho hr (f:CircleL2 T)).le
  have hb := circle_neutral_input_difference_bounds T e φ eN φN a f ε hε he0 heN ha
    heNH4 hφNH4 huNH4 heδ hφδ hz hzN hd (circle_finite_householder_hypotheses T).2.2
    hU (hchange.2.2.2 f).1.le
  refine ⟨hb.1,hb.2.1,hb.2.2.1,hb.2.2.2.1,hb.2.2.2.2.1,hb.2.2.2.2.2,?_,?_,?_⟩
  · have hu := (circle_householder_difference_bounds T e eN a f ε hε he0 heN ha huNH4
      heδ hd (circle_finite_householder_hypotheses T).2.2).1
    change circleAngularH4Norm T (neutralHouseholderDomain e a f-neutralHouseholderDomain eN a f) ≤ 5000*ε*‖f‖
    nlinarith only [hu,mul_nonneg hε (norm_nonneg f)]
  · exact hU.trans (by nlinarith only [norm_nonneg f])
  · exact (hchange.2.2.2 f).1.le.trans (by nlinarith only [norm_nonneg f])

end Lemniscate
