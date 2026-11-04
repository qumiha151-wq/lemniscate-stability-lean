import Lemniscate.PeriodicParabolicSpace
import Lemniscate.PeriodicSobolevH2Interpolation
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.L2Space

/-! Unit-time estimates for the physical velocity in the parabolic space.
The probability-measure L2-to-L1 comparison is the existing Holder estimate.
Together with the actual primitive identity it bounds the value at every
time, so the spatial H2 interpolation inequality can be integrated directly.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal Topology

private theorem unit_time_l2_integrable {E : Type*} [NormedAddCommGroup E]
    (f : Lp E 2 (volume : Measure unitInterval)) : Integrable f volume :=
  memLp_one_iff_integrable.mp ((Lp.memLp f).mono_exponent (by norm_num : (1:ℝ≥0∞) ≤ 2))

private theorem unit_time_integral_norm_le {E : Type*} [NormedAddCommGroup E]
    (f : Lp E 2 (volume : Measure unitInterval)) :
    (∫ t, ‖f t‖ ∂volume) ≤ ‖f‖ := by
  rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f),
    ← eLpNorm_one_eq_lintegral_enorm]
  change (eLpNorm f 1 volume).toReal ≤ (eLpNorm f 2 volume).toReal
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1:ℝ≥0∞) ≤ 2)
      (Lp.aestronglyMeasurable f))

theorem unit_time_l2_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (f : Lp E 2 (volume : Measure unitInterval)) :
    ‖f‖^2 = ∫ t, ‖f t‖^2 ∂volume := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) f f)]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => (norm_sq_eq_re_inner (𝕜 := ℂ) (f t)).symm

variable (T : ℝ) [Fact (0 < T)]

local instance circleParabolicEstimateSecondCountable :
    SecondCountableTopologyEither unitInterval (CircleSobolevSpace T 2) where
  out := Or.inl (inferInstance : SecondCountableTopology unitInterval)

/-- The actual indefinite integral is a contraction from time L2 to spatial L2. -/
theorem circle_time_integral_norm_le (t : unitInterval) :
    ‖circleTimeIntegral T t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0:ℝ) ≤ 1)
  intro v
  rw [one_mul,circle_time_integral_apply]
  calc
    ‖∫ r in Iic t, v r ∂volume‖ ≤ ∫ r in Iic t, ‖v r‖ ∂volume :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ r, ‖v r‖ ∂volume :=
      integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall fun r => norm_nonneg (v r))
        (unit_time_l2_integrable v).norm
    _ ≤ ‖v‖ := unit_time_integral_norm_le v

variable (τ : ℝ)

def circleParabolicH2Time :
    CircleParabolicSpace T τ →L[ℂ]
      Lp (CircleSobolevSpace T 2) 2 (volume : Measure unitInterval) :=
  (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℂ).comp (circleParabolicCurve T τ)

def circleParabolicValueTime : CircleParabolicSpace T τ →L[ℂ] CircleTimeL2 T :=
  ((circleSobolevCoordinate T 2 0).compLpL 2 (volume : Measure unitInterval)).comp
    (circleParabolicH2Time T τ)

private theorem circle_parabolic_h2_time_ae (u : CircleParabolicSpace T τ) :
    (circleParabolicH2Time T τ u : unitInterval → CircleSobolevSpace T 2) =ᵐ[volume]
      circleParabolicCurve T τ u :=
  ContinuousMap.coeFn_toLp (p := 2) (volume : Measure unitInterval) (𝕜 := ℂ)
    (circleParabolicCurve T τ u)

private theorem circle_parabolic_value_time_ae (u : CircleParabolicSpace T τ) :
    (circleParabolicValueTime T τ u : unitInterval → CircleL2 T) =ᵐ[volume]
      fun t => circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ u t) := by
  simp only [circleParabolicValueTime,ContinuousLinearMap.comp_apply]
  have hc := (circleSobolevCoordinate T 2 0).coeFn_compLpL
    (p := 2) (μ := (volume : Measure unitInterval)) (circleParabolicH2Time T τ u)
  filter_upwards [hc,circle_parabolic_h2_time_ae T τ u] with t ht hu
  simpa only [hu] using ht

/-- The H2 curve is the actual H2 inclusion of the H4 representative almost everywhere. -/
theorem circle_parabolic_h2_h4_ae (u : CircleParabolicSpace T τ) :
    ∀ᵐ t ∂(volume : Measure unitInterval),
      circleParabolicCurve T τ u t =
        circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (circleParabolicH4 T τ u t)) := by
  filter_upwards [circle_parabolic_value_ae T τ u] with t ht
  apply circle_sobolev_value_injective T 2
  change circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ u t) =
    circleSobolevCoordinate T 4 0 (circleParabolicH4 T τ u t)
  exact ht

private theorem circle_parabolic_zero_initial_value_bound
    (hτ : 0 ≤ τ) (u : CircleParabolicSpace T τ)
    (hu : circleParabolicInitialValue T τ u = 0) (t : unitInterval) :
    ‖circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ u t)‖ ≤
      τ*‖circleParabolicTimeDerivative T τ u‖ := by
  let C : C(unitInterval, CircleSobolevSpace T 2) := circleParabolicCurve T τ u
  let v : CircleTimeL2 T := circleParabolicTimeDerivative T τ u
  let E : CircleSobolevSpace T 2 →L[ℂ] CircleL2 T := circleSobolevCoordinate T 2 0
  have hzero : circleParabolicCurve T τ u 0 = 0 := by
    simpa only [circle_parabolic_initial_value_apply] using hu
  have hvaluezero : E (C 0) = 0 := by
    calc
      E (C 0) = E (0 : CircleSobolevSpace T 2) := congrArg E hzero
      _ = 0 := E.map_zero
  have hid : E (C t)-E (C 0) = τ • (∫ r in Iic t, v r ∂volume) :=
    circle_parabolic_integral_identity T τ u t
  have hInt : τ • circleTimeIntegral T t v = τ • (∫ r in Iic t, v r ∂volume) :=
    congrArg (fun z : CircleL2 T => τ • z) (circle_time_integral_apply T t v)
  have hvalue : E (C t) = τ • circleTimeIntegral T t v := by
    calc
      E (C t) = E (C t)-E (C 0) := by rw [hvaluezero,sub_zero]
      _ = τ • (∫ r in Iic t, v r ∂volume) := hid
      _ = τ • circleTimeIntegral T t v := hInt.symm
  have hcontract : ‖circleTimeIntegral T t v‖ ≤ ‖v‖ := by
    simpa only [one_mul] using (circleTimeIntegral T t).le_of_opNorm_le
      (circle_time_integral_norm_le T t) v
  change ‖E (C t)‖ ≤ τ*‖v‖
  calc
    ‖E (C t)‖ = ‖τ • circleTimeIntegral T t v‖ := congrArg norm hvalue
    _ = τ*‖circleTimeIntegral T t v‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hτ]
    _ ≤ τ*‖v‖ := mul_le_mul_of_nonneg_left hcontract hτ

/-- A zero initial value gives the time-L2 value estimate with the physical time length. -/
theorem circle_parabolic_zero_initial_value_time_bound
    (hτ : 0 ≤ τ) (u : CircleParabolicSpace T τ)
    (hu : circleParabolicInitialValue T τ u = 0) :
    ‖circleParabolicValueTime T τ u‖ ≤ τ*‖circleParabolicTimeDerivative T τ u‖ := by
  let V := circleParabolicValueTime T τ u
  let d := circleParabolicTimeDerivative T τ u
  have hVint : Integrable (fun t : unitInterval => ‖V t‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable V)).mp (Lp.memLp V)
  have hsq : ‖V‖^2 ≤ (τ*‖d‖)^2 := by
    rw [unit_time_l2_norm_sq]
    calc
      (∫ t, ‖V t‖^2 ∂volume) ≤ ∫ _ : unitInterval, (τ*‖d‖)^2 ∂volume := by
        apply integral_mono_ae hVint (integrable_const _)
        filter_upwards [circle_parabolic_value_time_ae T τ u] with t ht
        apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hτ (norm_nonneg d))).mpr
        change ‖circleParabolicValueTime T τ u t‖ ≤ _
        rw [ht]
        exact circle_parabolic_zero_initial_value_bound T τ hτ u hu t
      _ = (τ*‖d‖)^2 := by simp
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hτ (norm_nonneg d))).mp hsq

/-- The time H2 norm is small relative to the physical velocity and H4 norms
when the initial value vanishes. No new weighted parabolic norm is used. -/
theorem circle_parabolic_zero_initial_h2_time_interpolation
    (hτ : 0 ≤ τ) (u : CircleParabolicSpace T τ)
    (hu : circleParabolicInitialValue T τ u = 0) :
    ‖circleParabolicH2Time T τ u‖^2 ≤
      3*τ*‖circleParabolicTimeDerivative T τ u‖*‖circleParabolicH4 T τ u‖ := by
  let U := circleParabolicH2Time T τ u
  let W := circleParabolicH4 T τ u
  let d := circleParabolicTimeDerivative T τ u
  have hU : Integrable (fun t : unitInterval => ‖U t‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable U)).mp (Lp.memLp U)
  have hW : Integrable (fun t : unitInterval => ‖W t‖) volume :=
    (unit_time_l2_integrable W).norm
  have hpoint : ∀ᵐ t ∂(volume : Measure unitInterval),
      ‖U t‖^2 ≤ (3*τ*‖d‖)*‖W t‖ := by
    filter_upwards [circle_parabolic_h2_time_ae T τ u,circle_parabolic_h2_h4_ae T τ u,
      circle_parabolic_value_ae T τ u] with t hUt hWt hvalue
    have hnorm : ‖circleSobolevCoordinate T 4 0 (W t)‖ ≤ τ*‖d‖ := by
      rw [← hvalue]
      exact circle_parabolic_zero_initial_value_bound T τ hτ u hu t
    calc
      ‖U t‖^2 =
          ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (W t))‖^2 := by
        rw [hUt,hWt]
      _ ≤ 3*‖circleSobolevCoordinate T 4 0 (W t)‖*‖W t‖ :=
        circle_sobolev_h2_interpolation T (W t)
      _ ≤ 3*(τ*‖d‖)*‖W t‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm (by norm_num))
          (norm_nonneg (W t))
      _ = (3*τ*‖d‖)*‖W t‖ := by ring
  calc
    ‖U‖^2 = ∫ t, ‖U t‖^2 ∂volume := unit_time_l2_norm_sq U
    _ ≤ ∫ t, (3*τ*‖d‖)*‖W t‖ ∂volume :=
      integral_mono_ae hU (hW.const_mul _) hpoint
    _ = (3*τ*‖d‖)*(∫ t, ‖W t‖ ∂volume) := by rw [integral_const_mul]
    _ ≤ (3*τ*‖d‖)*‖W‖ :=
      mul_le_mul_of_nonneg_left (unit_time_integral_norm_le W) (by positivity)

end Lemniscate
