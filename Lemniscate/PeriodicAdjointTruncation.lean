import Lemniscate.PeriodicFiniteTruncation
import Lemniscate.PeriodicFixedTrialError

set_option maxHeartbeats 800000

/-! The fixed adjoint approximation after keeping fifteen modes and
renormalizing: residual error, three omitted modes, and rescaling error. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

noncomputable def adjointNormalizedCoefficient (j : Fin 18) : ℝ :=
  (adjointTrialCoefficient j:ℝ)/adjointTrialPairing

variable (T : ℝ) [Fact (0 < T)]

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = thetaParameter)

include hq hp he hqreal hpreal hs hc hr in
private theorem normalized_trial_coefficients :
    circleNormalizedTrial T (-circleUnitRotation T q p) (circleAdjointTrial T) =
      circleSineTrialH4 T 18 (fun j => (adjointNormalizedCoefficient j:ℂ)) := by
  rw [circleNormalizedTrial,
    circle_adjoint_trial_rotation_pairing T q p hq hp he hqreal hpreal hs hc hr]
  simp only [Complex.conj_ofReal,circleAdjointTrial,circleSineTrialH4,
    Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [adjointNormalizedCoefficient,Complex.ofReal_div,Complex.ofReal_ratCast,div_eq_mul_inv]
  push_cast
  ring

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_adjoint_truncation_h4_error (ψ : circleH4Domain T)
    (hψnorm : inner ℂ (ψ : CircleL2 T) (-circleUnitRotation T q p) = 1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (hψsector : InCircleEvenSineSector T (ψ : CircleL2 T)) (c : ℂ) :
    circleAngularH4Norm T (ψ-c • circleSineTrialH4 T 15
      (fun j => (adjointNormalizedCoefficient (Fin.castAdd 3 j):ℂ))) <
      (∑ j : Fin 3, |adjointNormalizedCoefficient (Fin.natAdd 15 j)| *
        ∑ k : Fin 5, (2*(15+j.val+1:ℕ):ℝ)^k.val)+
      ‖1-c‖ * (∑ j : Fin 15, |adjointNormalizedCoefficient (Fin.castAdd 3 j)| *
        ∑ k : Fin 5, (2*(j.val+1:ℕ):ℝ)^k.val)+(27:ℝ)/10^14 := by
  let t := circleNormalizedTrial T (-circleUnitRotation T q p) (circleAdjointTrial T)
  let g := circleSineTrialH4 T 15
    (fun j => (adjointNormalizedCoefficient (Fin.castAdd 3 j):ℂ))
  have hres := paper_fixed_adjoint_h4_error_sq T q p hq hp he hqreal hpreal hs hc ho hr
    ψ hψnorm hψzero hψsector
  have herr : circleAngularH4Norm T (ψ-t) < (27:ℝ)/10^14 := by
    change (circleAngularH4Norm T (ψ-t))^2 < _ at hres
    nlinarith only [hres]
  have hfinite := circle_finite_sine_truncation_error T 15 3
    (fun j => (adjointNormalizedCoefficient j:ℂ)) c
  rw [← normalized_trial_coefficients T q p hq hp he hqreal hpreal hs hc hr] at hfinite
  simp only [Complex.norm_real,Real.norm_eq_abs] at hfinite
  change circleAngularH4Norm T (ψ-c • g) < _
  have heq : ψ-c • g = (ψ-t)+(t-c • g) := by abel
  rw [heq]
  apply (circle_angular_h4_norm_add_le T _ _).trans_lt
  have h := add_lt_add_of_lt_of_le herr hfinite
  simpa only [add_comm,add_left_comm,add_assoc] using h

end Profile
end Lemniscate
