import Lemniscate.PeriodicTrialNormalization
import Lemniscate.PeriodicTrialSector
import Lemniscate.PeriodicAngularH4Norm

/-! The fixed trial's actual H4 error, with the positive sine convention
for the rotation vector used by the current manuscript. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem paper_fixed_adjoint_h4_error_sq (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ i : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*i+1) = 0)
    (hr : (2*Real.pi/T)^2 = thetaParameter) (ψ : circleH4Domain T)
    (hψnorm : inner ℂ (ψ : CircleL2 T) (-circleUnitRotation T q p) = 1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (hψsector : InCircleEvenSineSector T (ψ : CircleL2 T)) :
    (circleAngularH4Norm T
      (ψ-circleNormalizedTrial T (-circleUnitRotation T q p) (circleAdjointTrial T)))^2 <
        (62658:ℝ)/10^30 := by
  let t := circleNormalizedTrial T (-circleUnitRotation T q p) (circleAdjointTrial T)
  have hpair : inner ℂ (circleAdjointTrial T : CircleL2 T) (-circleUnitRotation T q p) ≠ 0 := by
    rw [circle_adjoint_trial_rotation_pairing T q p hq hp he hqreal hpreal hs hc hr]
    apply Complex.ofReal_ne_zero.mpr
    exact ne_of_gt (lt_trans (by norm_num : (0:ℝ) < 1) adjoint_trial_pairing_gt_one)
  have ht : inner ℂ (t : CircleL2 T) (-circleUnitRotation T q p) = 1 :=
    circle_normalized_trial_pairing T _ _ hpair
  have hts : InCircleEvenSineSector T (t : CircleL2 T) := by
    exact circle_even_sine_sector_smul T _ _ (circle_sine_trial_sector T 18
      (fun j => (adjointTrialCoefficient j:ℂ)))
  have hψn : inner ℂ ((-ψ : circleH4Domain T) : CircleL2 T) (circleUnitRotation T q p) = 1 := by
    simpa only [Submodule.coe_neg,inner_neg_left,inner_neg_right] using hψnorm
  have htn : inner ℂ ((-t : circleH4Domain T) : CircleL2 T) (circleUnitRotation T q p) = 1 := by
    simpa only [Submodule.coe_neg,inner_neg_left,inner_neg_right] using ht
  have hψz : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) (-ψ) = 0 := by
    rw [map_neg,hψzero,neg_zero]
  have hψs : InCircleEvenSineSector T ((-ψ : circleH4Domain T) : CircleL2 T) := by
    simpa only [neg_one_smul,Submodule.coe_neg] using
      circle_even_sine_sector_smul T (-1) (ψ : CircleL2 T) hψsector
  have htns : InCircleEvenSineSector T ((-t : circleH4Domain T) : CircleL2 T) := by
    simpa only [neg_one_smul,Submodule.coe_neg] using
      circle_even_sine_sector_smul T (-1) (t : CircleL2 T) hts
  have hb := paper_adjoint_trial_h4_error T q p hq hp he hqreal hpreal hs hc ho hr
    (-ψ) (-t) hψn htn hψz hψs htns
  have hneg (f : circleH4Domain T) : circleAngularH4Norm T (-f) = circleAngularH4Norm T f := by
    simpa only [neg_one_smul,norm_neg,norm_one,one_mul] using
      circle_angular_h4_norm_smul T (-1) f
  rw [show -ψ-(-t) = -(ψ-t) by abel,hneg,map_neg,norm_neg] at hb
  have hb2 := pow_le_pow_left₀ (circle_angular_h4_norm_nonneg T (ψ-t)) hb 2
  have hres := circle_normalized_adjoint_trial_residual_sq T q p hq hp he hqreal hpreal
    hs hc hr ho (-1) (by norm_num)
  simp only [neg_one_smul] at hres
  change (circleAngularH4Norm T (ψ-t))^2 < _
  change ‖circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) t‖^2 < _ at hres
  nlinarith only [hb2,hres]

end Lemniscate
