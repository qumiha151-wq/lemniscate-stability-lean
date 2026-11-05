import Lemniscate.ShortAdjointApproximationError

/-! Coarse bounds for the genuine vectors retain the finite certificate's
strict margin; no true-vector bound is inferred by discarding a tail. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem short_rotation_v_margin :
    (shortSevenSquareInput shortRotationSineInput CoarseArithmetic.shortVWeight).hi < 24 :=
  by decide +kernel

private theorem short_rotation_finite_v_margin :
    shortVNorm T (circleShortRotationApproximation T) < (49/10:ℝ) := by
  have h := short_seven_square_bound shortRotationSineInput
    (shortRotationSine shortActualCoefficient) CoarseArithmetic.shortVWeight 24
      short_rotation_sine_input_sound short_rotation_v_margin
  have hn := (short_sine_trial_norms_sq T
    (fun i : Fin 7 => (shortRotationSine shortActualCoefficient i:ℂ))).2.2
  have hs : shortVNorm T (circleShortRotationApproximation T)^2 < 24 := by
    rw [circleShortRotationApproximation,short_v_norm_smul,Complex.norm_I,one_mul,hn]
    simpa [CoarseArithmetic.shortVWeight,Complex.norm_real,Real.norm_eq_abs,sq_abs] using h
  nlinarith only [hs,short_v_norm_nonneg T (circleShortRotationApproximation T)]

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

theorem short_actual_adjoint_vector_bounds (ψ : circleH4Domain T)
    (hψnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p) = 1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (hψsector : InCircleEvenSineSector T (ψ:CircleL2 T)) :
    shortVNorm T (circleShortRotationVector T q p hq hp) ≤ 5 ∧
      ‖((circleShortAdjointVector T ψ-circleShortRotationVector T q p hq hp:
        circleH4Domain T):CircleL2 T)‖ ≤ (51/1000:ℝ) ∧
      shortH1Norm T (circleShortAdjointVector T ψ-circleShortRotationVector T q p hq hp) ≤
        (1/4:ℝ) := by
  let e := circleShortRotationVector T q p hq hp
  let E := circleShortRotationApproximation T
  let Ψ := circleShortAdjointVector T ψ
  let ΨN := circleShortAdjointApproximation T
  have herr := short_actual_rotation_approximation_error T q p hq hp he hqreal hpreal hs hc ho hr
  have hperr := short_actual_adjoint_approximation_error T q p hq hp he hqreal hpreal hs hc ho hr
    ψ hψnorm hψzero hψsector
  have hf := short_actual_finite_vector_bounds T
  have hV := short_v_norm_add_le T (e-E) E
  rw [sub_add_cancel] at hV
  have hVfinite := short_rotation_finite_v_margin T
  have hz : Ψ-e = ((Ψ-ΨN)+(ΨN-E))-(e-E) := by module
  have h0 : ‖((Ψ-e:circleH4Domain T):CircleL2 T)‖ ≤
      ‖((Ψ-ΨN:circleH4Domain T):CircleL2 T)‖+
      ‖((ΨN-E:circleH4Domain T):CircleL2 T)‖+
      ‖((e-E:circleH4Domain T):CircleL2 T)‖ := by
    rw [hz]
    exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have h1 : shortH1Norm T (Ψ-e) ≤ shortH1Norm T (Ψ-ΨN)+
      shortH1Norm T (ΨN-E)+shortH1Norm T (e-E) := by
    change shortH1Seminorm T (Ψ-e) ≤ shortH1Seminorm T (Ψ-ΨN)+
      shortH1Seminorm T (ΨN-E)+shortH1Seminorm T (e-E)
    rw [hz]
    exact (map_sub_le_add (shortH1Seminorm T) _ _).trans
      (add_le_add (map_add_le_add (shortH1Seminorm T) _ _) le_rfl)
  refine ⟨?_,?_,?_⟩
  · change shortVNorm T e ≤ 5
    linarith only [hV,herr.2.2,hVfinite]
  · change ‖((Ψ-e:circleH4Domain T):CircleL2 T)‖ ≤ _
    linarith only [h0,hperr.1,herr.1,hf.2.2.2.2.2.1]
  · change shortH1Norm T (Ψ-e) ≤ _
    linarith only [h1,hperr.2,herr.2.1,hf.2.2.2.2.2.2]

end Profile
end Lemniscate
