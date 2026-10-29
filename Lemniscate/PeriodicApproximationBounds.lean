import Lemniscate.VectorErrorSoundness
import Lemniscate.PeriodicRotationTruncation

/-! Numerical H4 bounds for the actual rotation and adjoint eigenfunctions,
under the explicit profile hypotheses. Both use the same finite sine norms. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleRotationApproximation : circleH4Domain T :=
  circleSineTrialH4 T 15 (fun j => (rotationFiniteCoefficient j:ℂ))

noncomputable def circleAdjointApproximation : circleH4Domain T :=
  circleSineTrialH4 T 15 (fun j => (adjointFiniteCoefficient j:ℂ))

private theorem real_sine_rescale (N : ℕ) (v : Fin N → ℝ) (c : ℝ) :
    circleSineTrialH4 T N (fun j => ((v j/c:ℝ):ℂ)) =
      (c:ℂ)⁻¹ • circleSineTrialH4 T N (fun j => (v j:ℂ)) := by
  simp only [circleSineTrialH4,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  push_cast
  ring

theorem circle_sine_interval_norm_le {N : ℕ} (I : Fin N → Interval)
    (v : Fin N → ℝ) (hv : ∀ j, Contains (I j) (v j)) :
    circleAngularH4Norm T (circleSineTrialH4 T N (fun j => (v j:ℂ))) ≤
      (intervalL4 I:ℝ) := by
  have h := circle_sine_trial_angular_norm_le T N (fun j => (v j:ℂ))
  simp only [Complex.norm_real,Real.norm_eq_abs] at h
  exact h.trans (interval_l4_sound I v hv)

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

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_rotation_approximation_bounds :
    circleAngularH4Norm T (-circleUnitRotationH4 T q p hq hp-
      circleRotationApproximation T) < (2:ℝ)/10^12 ∧
    circleAngularH4Norm T (-circleUnitRotationH4 T q p hq hp) < 200 ∧
    circleAngularH4Norm T (circleRotationApproximation T) < 200 := by
  have hid : circleRotationApproximation T = (rotationFiniteNorm:ℂ)⁻¹ •
      circleSineTrialH4 T 15 (fun j => (rotationSineCoefficient j.val:ℂ)) :=
    real_sine_rescale T 15 (fun j => rotationSineCoefficient j.val) rotationFiniteNorm
  have h := circle_rotation_truncation_h4_error T q p hq hp he hqreal hpreal hs hc ho hr
    15 (rotationFiniteNorm:ℂ)⁻¹
  rw [← hid] at h
  have herr := h.trans rotation_error_expression_bound
  have hfinite : circleAngularH4Norm T (circleRotationApproximation T) ≤
      (intervalL4 rotationFiniteData:ℝ) :=
    circle_sine_interval_norm_le T _ _ rotation_finite_data_sound
  refine ⟨?_,?_,?_⟩
  · have hnum : (rotationErrorUpper:ℝ) < (2:ℝ)/10^12 := by
      have hx : (rotationErrorUpper:ℝ) < ((2/10^12:ℚ):ℝ) :=
        Rat.cast_lt.mpr vector_error_comparisons.1
      simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using hx
    exact herr.trans_lt hnum
  · have heq : -circleUnitRotationH4 T q p hq hp = circleRotationApproximation T+
        (-circleUnitRotationH4 T q p hq hp-circleRotationApproximation T) := by abel
    calc
      circleAngularH4Norm T (-circleUnitRotationH4 T q p hq hp) =
          circleAngularH4Norm T (circleRotationApproximation T+
            (-circleUnitRotationH4 T q p hq hp-circleRotationApproximation T)) := congrArg _ heq
      _ ≤ circleAngularH4Norm T (circleRotationApproximation T)+
          circleAngularH4Norm T (-circleUnitRotationH4 T q p hq hp-circleRotationApproximation T) :=
        circle_angular_h4_norm_add_le T _ _
      _ ≤ (intervalL4 rotationFiniteData:ℝ)+(rotationErrorUpper:ℝ) := add_le_add hfinite herr
      _ < 200 := by exact_mod_cast vector_error_comparisons.2.2.1
  · have hn : (intervalL4 rotationFiniteData:ℝ)+(rotationErrorUpper:ℝ) < 200 := by
      exact_mod_cast vector_error_comparisons.2.2.1
    have he0 := (circle_angular_h4_norm_nonneg T _).trans herr
    linarith only [hfinite,hn,he0]

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_adjoint_approximation_bounds (ψ : circleH4Domain T)
    (hψnorm : inner ℂ (ψ : CircleL2 T) (-circleUnitRotation T q p) = 1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (hψsector : InCircleEvenSineSector T (ψ : CircleL2 T)) :
    circleAngularH4Norm T (ψ-circleAdjointApproximation T) < (6:ℝ)/10^12 ∧
    circleAngularH4Norm T ψ < 200 ∧
    circleAngularH4Norm T (circleAdjointApproximation T) < 200 := by
  have hid : circleAdjointApproximation T = (adjointFinitePairing:ℂ)⁻¹ •
      circleSineTrialH4 T 15 (fun j => (adjointNormalizedCoefficient (Fin.castAdd 3 j):ℂ)) :=
    real_sine_rescale T 15 (fun j => adjointNormalizedCoefficient (Fin.castAdd 3 j)) adjointFinitePairing
  have h := paper_adjoint_truncation_h4_error T q p hq hp he hqreal hpreal hs hc ho hr
    ψ hψnorm hψzero hψsector (adjointFinitePairing:ℂ)⁻¹
  rw [← hid] at h
  have herr := h.trans_le adjoint_error_expression_bound
  have hfinite : circleAngularH4Norm T (circleAdjointApproximation T) ≤
      (intervalL4 adjointFiniteData:ℝ) :=
    circle_sine_interval_norm_le T _ _ adjoint_finite_data_sound
  refine ⟨?_,?_,?_⟩
  · have hnum : (adjointErrorUpper:ℝ) < (6:ℝ)/10^12 := by
      have hx : (adjointErrorUpper:ℝ) < ((6/10^12:ℚ):ℝ) :=
        Rat.cast_lt.mpr vector_error_comparisons.2.1
      simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using hx
    exact herr.trans hnum
  · have heq : ψ = circleAdjointApproximation T+(ψ-circleAdjointApproximation T) := by abel
    calc
      circleAngularH4Norm T ψ =
          circleAngularH4Norm T (circleAdjointApproximation T+(ψ-circleAdjointApproximation T)) :=
        congrArg _ heq
      _ ≤ circleAngularH4Norm T (circleAdjointApproximation T)+
          circleAngularH4Norm T (ψ-circleAdjointApproximation T) :=
        circle_angular_h4_norm_add_le T _ _
      _ ≤ (intervalL4 adjointFiniteData:ℝ)+(adjointErrorUpper:ℝ) := add_le_add hfinite herr.le
      _ < 200 := by exact_mod_cast vector_error_comparisons.2.2.2.1
  · have hn : (intervalL4 adjointFiniteData:ℝ)+(adjointErrorUpper:ℝ) < 200 := by
      exact_mod_cast vector_error_comparisons.2.2.2.1
    have he0 := (circle_angular_h4_norm_nonneg T _).trans herr.le
    linarith only [hfinite,hn,he0]

end Profile
end Lemniscate
