import Lemniscate.PeriodicCoverStableMetric
import Lemniscate.PeriodicBlochReflection

/-! The actual Bloch operator is dissipative in the signed centered metric.
The proof transports the already established full centered energy through
the actual H4-domain inverse. The zero block uses the neutral transform
alone and retains the full stable gap on the adjoint-kernel complement.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)
include hq hp he hqreal hpreal hs hc ho hr

private theorem paper_positive_bloch_metric_energy (ψ : circleH4Domain T)
    (hnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p) = 1)
    (hzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (hd : HasCircleNeutralDecomposition T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circleUnitRotationH4 T q p hq hp) (ψ:CircleL2 T))
    (α : ℝ) (hα0 : 0 ≤ α) (hαhalf : α ≤ 1/2) (f : circleH4Domain T) :
    let P := circleCenteredL2Equiv T q p hq hp he hqreal hpreal hs hc ho hr
      (ψ:CircleL2 T) hnorm
    (inner ℂ (P (f:CircleL2 T))
      (P (circleBlochOperator T (q^2) ((2:ℂ) • (q*p))
        (1-(3:ℂ) • (q^4)) α f))).re ≤
      -(α^2/2)*‖P (f:CircleL2 T)‖^2 := by
  let e := circleUnitRotationH4 T q p hq hp
  let U₄ := circleRotationHouseholderH4 T q p hq hp
  let P := circleCenteredL2Equiv T q p hq hp he hqreal hpreal hs hc ho hr
    (ψ:CircleL2 T) hnorm
  let g : circleH4Domain T := U₄ (neutralTransformDomain e (ψ:CircleL2 T) f)
  have hginv : neutralTransformInvDomain e (ψ:CircleL2 T) (U₄ g) = f := by
    dsimp only [g,U₄]
    rw [paper_householder_h4_involutive T q p hq hp he hqreal hpreal hs hc ho hr]
    exact (hd.2.1 f).2
  have hg : (g:CircleL2 T) = P (f:CircleL2 T) := by
    change (circleRotationHouseholderH4 T q p hq hp
      (neutralTransformDomain e (ψ:CircleL2 T) f) : CircleL2 T) = _
    rw [circle_rotation_householder_h4_coe,neutral_transform_domain_coe]
    rfl
  have hB : circleCenteredBlochOperator T q p hq hp (ψ:CircleL2 T) α g =
      P (circleBlochOperator T (q^2) ((2:ℂ) • (q*p))
        (1-(3:ℂ) • (q^4)) α f) := by
    change circleRotationHouseholder T q p
      (neutralTransform e (ψ:CircleL2 T)
        (circleBlochOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) α
          (neutralTransformInvDomain e (ψ:CircleL2 T) (U₄ g)))) = _
    rw [hginv]
    rfl
  have h := paper_centered_full_bloch_energy T q p hq hp he hqreal hpreal hs hc ho hr
    ψ hnorm hzero hd α hα0 hαhalf g
  simpa only [hg,hB] using h

/-- Both signs of the Bloch parameter satisfy the full metric energy bound.
The metric is U*T for nonnegative parameters and R*(U*T)*R for negative ones. -/
theorem paper_signed_bloch_metric_energy (ψ : circleH4Domain T)
    (hnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p) = 1)
    (hzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (hd : HasCircleNeutralDecomposition T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circleUnitRotationH4 T q p hq hp) (ψ:CircleL2 T))
    (α : ℝ) (hα : |α| ≤ 1/2) (f : circleH4Domain T) :
    let P := circleCenteredL2Equiv T q p hq hp he hqreal hpreal hs hc ho hr
      (ψ:CircleL2 T) hnorm
    let S : CircleL2 T → CircleL2 T :=
      if 0 ≤ α then (P : CircleL2 T → CircleL2 T)
      else fun z => circleReflect T (P (circleReflect T z))
    (inner ℂ (S (f:CircleL2 T))
      (S (circleBlochOperator T (q^2) ((2:ℂ) • (q*p))
        (1-(3:ℂ) • (q^4)) α f))).re ≤
      -(α^2/2)*‖S (f:CircleL2 T)‖^2 := by
  let P := circleCenteredL2Equiv T q p hq hp he hqreal hpreal hs hc ho hr
    (ψ:CircleL2 T) hnorm
  change (inner ℂ
    ((if 0 ≤ α then (P : CircleL2 T → CircleL2 T)
      else fun z => circleReflect T (P (circleReflect T z))) (f:CircleL2 T))
    ((if 0 ≤ α then (P : CircleL2 T → CircleL2 T)
      else fun z => circleReflect T (P (circleReflect T z)))
        (circleBlochOperator T (q^2) ((2:ℂ) • (q*p))
          (1-(3:ℂ) • (q^4)) α f))).re ≤
    -(α^2/2)*‖(if 0 ≤ α then (P : CircleL2 T → CircleL2 T)
      else fun z => circleReflect T (P (circleReflect T z))) (f:CircleL2 T)‖^2
  obtain ⟨hαlo,hαhi⟩ := abs_le.mp hα
  by_cases hα0 : 0 ≤ α
  · simp only [if_pos hα0]
    exact paper_positive_bloch_metric_energy T q p hq hp he hqreal hpreal hs hc ho hr
      ψ hnorm hzero hd α hα0 hαhi f
  · simp only [if_neg hα0]
    have h := paper_positive_bloch_metric_energy T q p hq hp he hqreal hpreal hs hc ho hr
      ψ hnorm hzero hd (-α) (by linarith) (by linarith) (circleReflectH4 T f)
    have hreflect :
        circleBlochOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
            (-α) (circleReflectH4 T f) =
          circleReflect T (circleBlochOperator T (q^2) ((2:ℂ) • (q*p))
            (1-(3:ℂ) • (q^4)) α f) := by
      simpa only [neg_neg] using circle_bloch_reflect T _ _ _
        (circle_profile_square_deriv T q p hq)
        (circle_profile_square_second T q p hq hp he) hs (-α) f
    change (inner ℂ (P (circleReflectH4 T f:CircleL2 T))
      (P (circleBlochOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
        (-α) (circleReflectH4 T f)))).re ≤
      -((-α)^2/2)*‖P (circleReflectH4 T f:CircleL2 T)‖^2 at h
    rw [hreflect,circle_reflect_h4_coe] at h
    rw [circle_reflect_inner,circle_reflect_norm]
    simpa only [neg_sq] using h

/-- The zero Bloch block retains the full stable gap in the neutral metric T.
The adjoint pairing removes the actual rotation mode before dissipation. -/
theorem paper_zero_bloch_metric_energy (ψ : CircleL2 T)
    (hd : HasCircleNeutralDecomposition T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circleUnitRotationH4 T q p hq hp) ψ)
    (f : circleH4Domain T) (hstable : inner ℂ ψ (f:CircleL2 T) = 0) :
    let Z := neutralTransform (circleUnitRotationH4 T q p hq hp) ψ
    (inner ℂ (Z (f:CircleL2 T))
      (Z (circleBlochOperator T (q^2) ((2:ℂ) • (q*p))
        (1-(3:ℂ) • (q^4)) 0 f))).re ≤
      -(21/4:ℝ)*‖Z (f:CircleL2 T)‖^2 := by
  let e := circleUnitRotationH4 T q p hq hp
  let Z := neutralTransform e ψ
  let v : circleH4Domain T := neutralTransformDomain e ψ f
  let N := paperSinglePeriodNeutralOperator T q p hq hp he hqreal hpreal hs hc ho hr
  have hunit : inner ℂ (e:CircleL2 T) (e:CircleL2 T) = 1 := N.inner_neutral_self
  have horth : inner ℂ (e:CircleL2 T) (v:CircleL2 T) = 0 := by
    change inner ℂ (e:CircleL2 T) (neutralTransform e ψ (f:CircleL2 T)) = 0
    rw [neutral_transform_pairing e ψ hunit]
    exact hstable
  have hinv : neutralTransformInvDomain e ψ v = f := (hd.2.1 f).2
  have htrans : Z (circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) f) =
      circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) v-
        inner ℂ (e:CircleL2 T)
          (circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) v) •
            (e:CircleL2 T) := by
    have h := hd.2.2.1 v
    rw [hinv] at h
    exact h
  have hcoe : Z (f:CircleL2 T) = (v:CircleL2 T) :=
    (neutral_transform_domain_coe e ψ f).symm
  have h := N.dissipative v horth
  change (inner ℂ (v:CircleL2 T)
    (circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) v)).re ≤
      -(21/4:ℝ)*‖(v:CircleL2 T)‖^2 at h
  change (inner ℂ (Z (f:CircleL2 T))
    (Z (circleBlochOperator T (q^2) ((2:ℂ) • (q*p))
      (1-(3:ℂ) • (q^4)) 0 f))).re ≤ -(21/4:ℝ)*‖Z (f:CircleL2 T)‖^2
  rw [hcoe,circle_bloch_at_zero,htrans,inner_sub_right,inner_smul_right,
    inner_eq_zero_symm.mpr horth,mul_zero,sub_zero]
  exact h

end Profile
end Lemniscate
