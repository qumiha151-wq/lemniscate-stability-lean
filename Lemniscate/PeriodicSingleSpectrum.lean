import Lemniscate.PeriodicFullEnergy
import Lemniscate.PeriodicRotationDomain
import Lemniscate.PeriodicFredholmAlternative
import Lemniscate.NeutralNormalization

/-! The single-period kernel and full spectral gap for the actual H4 operator.
The operator is instantiated in the abstract neutral-mode argument using proved
coercivity and a proved nonzero rotation vector. Jacobi data remain explicit. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_sine_constraint_ne_zero : circleSineConstraintVector T ≠ 0 := by
  intro hz
  have hc := circle_sine_constraint_coeff_first T
  rw [hz, circle_fourierCoeff_zero] at hc
  exact evenSineFactor_ne_zero hc.symm

theorem circle_profile_rotation_ne_zero (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ i : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*i+1) = 0) :
    circleContinuousL2 T (q*p) ≠ 0 := by
  have hcp (j : ℕ) (hj : 0 < j) :
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
        (evenCoefficient thetaParameter nome j:ℂ) := by
    simpa only [fourierCoefficient, if_neg (Nat.ne_of_gt hj)] using hc j
  have hr := circle_sine_rotation_derivative T (q^2) ((2:ℂ) • (q*p))
    (circle_profile_square_deriv T q p hq) hs hcp ho
  rw [circle_continuous_l2_smul] at hr
  intro hz
  rw [hz, smul_zero] at hr
  rcases smul_eq_zero.mp hr.symm with hscale | hvec
  · exact circle_sine_rotation_scale_ne_zero T hscale
  · exact circle_sine_constraint_ne_zero T hvec

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

noncomputable def paperSinglePeriodNeutralOperator : NeutralCoerciveOperator (CircleL2 T) :=
  normalizedNeutralCoerciveOperator (circleH4Domain T)
    (circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)))
    (circleRotationH4 T q p hq hp) (circle_profile_rotation_ne_zero T q p hq hs hc ho)
    (circle_rotation_h4_kernel T q p hq hp he) (21/4) (by norm_num)
    (fun f hf => paper_h4_operator_rotation_complement_dissipative T q p hq hp he
      hqreal hpreal hs hc ho hr f hf)

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_single_period_kernel (f : circleH4Domain T)
    (hf : circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) f = 0) :
    ∃ c : ℂ, (f : CircleL2 T) = c • circleContinuousL2 T (q*p) := by
  let N := paperSinglePeriodNeutralOperator T q p hq hp he hqreal hpreal hs hc ho hr
  have hk := N.kernel_is_neutral f hf
  have hk' := congrArg (fun z : circleH4Domain T => (z : CircleL2 T)) hk
  change (f : CircleL2 T) =
    (inner ℂ (N.neutral : CircleL2 T) (f : CircleL2 T)) •
      (((‖circleContinuousL2 T (q*p)‖:ℂ)⁻¹) • circleContinuousL2 T (q*p)) at hk'
  rw [smul_smul] at hk'
  exact ⟨_, hk'⟩

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_single_period_no_generalized_kernel (f g : circleH4Domain T)
    (hfg : circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) f = (g : CircleL2 T))
    (hg : circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) g = 0) :
    circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) f = 0 :=
  (paperSinglePeriodNeutralOperator T q p hq hp he hqreal hpreal hs hc ho hr).no_generalized_neutral
    f g hfg hg

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_single_period_nonzero_spectral_bound (z : ℂ) (hz : z ≠ 0)
    (hmem : z ∈ circleSpectrum T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))) :
    z.re ≤ -(21/4:ℝ) := by
  obtain ⟨f, hf, hAf⟩ := (circle_spectrum_iff_eigenvector T (q^2) ((2:ℂ) • (q*p))
    (1-(3:ℂ) • (q^4)) z).mp hmem
  exact (paperSinglePeriodNeutralOperator T q p hq hp he hqreal hpreal hs hc ho hr).nonzero_eigenvalue_bound
    f z hf hz hAf

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_single_period_spectral_gap_five (z : ℂ) (hz : z ≠ 0)
    (hmem : z ∈ circleSpectrum T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))) :
    z.re ≤ -5 := by
  have hb := paper_single_period_nonzero_spectral_bound T q p hq hp he hqreal hpreal hs hc ho hr z hz hmem
  linarith

include hq hp he hs hc ho in
theorem paper_single_period_zero_mem_spectrum :
    (0:ℂ) ∈ circleSpectrum T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) := by
  apply (circle_spectrum_iff_eigenvector T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) 0).mpr
  refine ⟨circleRotationH4 T q p hq hp, circle_profile_rotation_ne_zero T q p hq hs hc ho, ?_⟩
  rw [circle_rotation_h4_kernel T q p hq hp he, zero_smul]

end Profile
end Lemniscate
