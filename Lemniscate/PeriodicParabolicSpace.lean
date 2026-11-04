import Lemniscate.PeriodicSobolevSpace
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Operator.Mul

/-! A complete maximal-regularity space on the actual unit time interval.
The continuous H2 curve and the L2-in-time H4 representative have the same
L2 value almost everywhere. For a physical time length tau, the physical
velocity satisfies u(t)-u(0) = tau * integral_0^t v on the unit interval.
Both conditions are closed linear constraints in the same product norm.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal Topology

variable (T : ℝ) [Fact (0 < T)]

local instance circleParabolicTimeSecondCountable :
    SecondCountableTopologyEither unitInterval (CircleSobolevSpace T 2) where
  out := Or.inl (inferInstance : SecondCountableTopology unitInterval)

abbrev CircleTimeL2 := Lp (CircleL2 T) 2 (volume : Measure unitInterval)

abbrev CircleTimeH4 := Lp (CircleSobolevSpace T 4) 2 (volume : Measure unitInterval)

abbrev CircleParabolicAmbient :=
  C(unitInterval, CircleSobolevSpace T 2) × (CircleTimeH4 T × CircleTimeL2 T)

/-- The actual integral up to time t, as a continuous linear map on time L2.
`lpPairing` is defined by the Holder map L2 x L2 -> L1 followed by the
Bochner `L1.integralCLM'`; the first factor here is the interval indicator. -/
def circleTimeIntegral (t : unitInterval) : CircleTimeL2 T →L[ℂ] CircleL2 T :=
  ((ContinuousLinearMap.lsmul ℂ ℂ :
      ℂ →L[ℂ] CircleL2 T →L[ℂ] CircleL2 T).lpPairing
      (volume : Measure unitInterval) 2 2)
    (indicatorConstLp 2 (measurableSet_Iic : MeasurableSet (Iic t))
      (measure_ne_top volume _) (1:ℂ))

theorem circle_time_integral_apply (t : unitInterval) (v : CircleTimeL2 T) :
    circleTimeIntegral T t v = ∫ r in Iic t, v r ∂volume := by
  have hi :
      (indicatorConstLp 2 (measurableSet_Iic : MeasurableSet (Iic t))
          (measure_ne_top volume _) (1:ℂ) : unitInterval → ℂ) =ᵐ[volume]
        (Iic t).indicator (fun _ : unitInterval => (1:ℂ)) :=
    indicatorConstLp_coeFn
  rw [circleTimeIntegral,ContinuousLinearMap.lpPairing_eq_integral,
    ← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  filter_upwards [hi] with r hr
  simp only [ContinuousLinearMap.lsmul_apply,hr]
  by_cases hrt : r ∈ Iic t <;> simp [hrt]

private def circleParabolicAmbientCurve :
    CircleParabolicAmbient T →L[ℂ] C(unitInterval, CircleSobolevSpace T 2) :=
  ContinuousLinearMap.fst ℂ _ _

private def circleParabolicAmbientH4 : CircleParabolicAmbient T →L[ℂ] CircleTimeH4 T :=
  (ContinuousLinearMap.fst ℂ (CircleTimeH4 T) (CircleTimeL2 T)).comp
    (ContinuousLinearMap.snd ℂ C(unitInterval, CircleSobolevSpace T 2) _)

private def circleParabolicAmbientTimeDerivative :
    CircleParabolicAmbient T →L[ℂ] CircleTimeL2 T :=
  (ContinuousLinearMap.snd ℂ (CircleTimeH4 T) (CircleTimeL2 T)).comp
    (ContinuousLinearMap.snd ℂ C(unitInterval, CircleSobolevSpace T 2) _)

private def circleParabolicValueConstraint :
    CircleParabolicAmbient T →L[ℂ] CircleTimeL2 T :=
  (((circleSobolevCoordinate T 2 0).compLpL 2 (volume : Measure unitInterval)).comp
      (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℂ)).comp
        (circleParabolicAmbientCurve T)-
    ((circleSobolevCoordinate T 4 0).compLpL 2 (volume : Measure unitInterval)).comp
      (circleParabolicAmbientH4 T)

variable (τ : ℝ)

private def circleParabolicTimeConstraint (t : unitInterval) :
    CircleParabolicAmbient T →L[ℂ] CircleL2 T :=
  (circleSobolevCoordinate T 2 0).comp
      ((((ContinuousMap.evalCLM ℂ t)-(ContinuousMap.evalCLM ℂ (0 : unitInterval))) :
          C(unitInterval, CircleSobolevSpace T 2) →L[ℂ] CircleSobolevSpace T 2).comp
        (circleParabolicAmbientCurve T))-
    τ • ((circleTimeIntegral T t).comp (circleParabolicAmbientTimeDerivative T))

def circleParabolicSubmodule : Submodule ℂ (CircleParabolicAmbient T) :=
  (circleParabolicValueConstraint T).ker ⊓
    ⨅ t : unitInterval, (circleParabolicTimeConstraint T τ t).ker

instance circleParabolicSubmodule_isClosed :
    IsClosed (circleParabolicSubmodule T τ : Set (CircleParabolicAmbient T)) := by
  simp only [circleParabolicSubmodule,Submodule.coe_inf,Submodule.coe_iInf]
  exact (circleParabolicValueConstraint T).isClosed_ker.inter
    (isClosed_iInter fun t => (circleParabolicTimeConstraint T τ t).isClosed_ker)

/-- The inherited product norm controls the continuous H2 curve, the time L2
H4 component, and the time L2 velocity. Closedness proves completeness. -/
abbrev CircleParabolicSpace := circleParabolicSubmodule T τ

instance circleParabolicSpace_completeSpace : CompleteSpace (CircleParabolicSpace T τ) :=
  inferInstance

def circleParabolicCurve :
    CircleParabolicSpace T τ →L[ℂ] C(unitInterval, CircleSobolevSpace T 2) :=
  (circleParabolicAmbientCurve T).comp (circleParabolicSubmodule T τ).subtypeL

def circleParabolicH4 : CircleParabolicSpace T τ →L[ℂ] CircleTimeH4 T :=
  (circleParabolicAmbientH4 T).comp (circleParabolicSubmodule T τ).subtypeL

def circleParabolicTimeDerivative : CircleParabolicSpace T τ →L[ℂ] CircleTimeL2 T :=
  (circleParabolicAmbientTimeDerivative T).comp (circleParabolicSubmodule T τ).subtypeL

def circleParabolicInitialValue : CircleParabolicSpace T τ →L[ℂ] CircleSobolevSpace T 2 :=
  (ContinuousMap.evalCLM ℂ (0 : unitInterval) :
    C(unitInterval, CircleSobolevSpace T 2) →L[ℂ] CircleSobolevSpace T 2).comp
      (circleParabolicCurve T τ)

@[simp] theorem circle_parabolic_initial_value_apply (u : CircleParabolicSpace T τ) :
    circleParabolicInitialValue T τ u = circleParabolicCurve T τ u 0 := rfl

theorem circle_parabolic_mem_iff (z : CircleParabolicAmbient T) :
    z ∈ circleParabolicSubmodule T τ ↔
      ((circleSobolevCoordinate T 2 0).compLpL 2 (volume : Measure unitInterval)
          (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℂ z.1) =
        (circleSobolevCoordinate T 4 0).compLpL 2 (volume : Measure unitInterval) z.2.1) ∧
      ∀ t : unitInterval,
        circleSobolevCoordinate T 2 0 (z.1 t)-circleSobolevCoordinate T 2 0 (z.1 0) =
          τ • (∫ r in Iic t, z.2.2 r ∂volume) := by
  simp only [circleParabolicSubmodule,Submodule.mem_inf,Submodule.mem_iInf]
  change
    (((circleSobolevCoordinate T 2 0).compLpL 2 (volume : Measure unitInterval)
          (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℂ z.1)-
        (circleSobolevCoordinate T 4 0).compLpL 2 (volume : Measure unitInterval) z.2.1 = 0) ∧
      ∀ t : unitInterval,
        circleSobolevCoordinate T 2 0 (z.1 t-z.1 0)-τ • circleTimeIntegral T t z.2.2 = 0) ↔ _
  simp only [map_sub,circle_time_integral_apply,sub_eq_zero]

/-- Agreement is an equality of actual almost-everywhere representatives. -/
theorem circle_parabolic_value_ae (u : CircleParabolicSpace T τ) :
    ∀ᵐ t ∂(volume : Measure unitInterval),
      circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ u t) =
        circleSobolevCoordinate T 4 0 (circleParabolicH4 T τ u t) := by
  change ∀ᵐ t ∂(volume : Measure unitInterval),
    circleSobolevCoordinate T 2 0 (u.1.1 t) =
      circleSobolevCoordinate T 4 0 (u.1.2.1 t)
  have heq := ((circle_parabolic_mem_iff T τ u.1).mp u.property).1
  have hc := (circleSobolevCoordinate T 2 0).coeFn_compLpL
    (p := 2) (μ := (volume : Measure unitInterval))
    (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℂ u.1.1)
  have hct := ContinuousMap.coeFn_toLp (p := 2)
    (volume : Measure unitInterval) (𝕜 := ℂ) u.1.1
  have hh := (circleSobolevCoordinate T 4 0).coeFn_compLpL
    (p := 2) (μ := (volume : Measure unitInterval)) u.1.2.1
  filter_upwards [hc,hct,hh] with t hcv hctv hhv
  rw [hctv] at hcv
  have ht := congrArg (fun f : CircleTimeL2 T => f t) heq
  exact hcv.symm.trans (ht.trans hhv)

theorem circle_parabolic_time_derivative_integrable (u : CircleParabolicSpace T τ) :
    Integrable (circleParabolicTimeDerivative T τ u) (volume : Measure unitInterval) :=
  memLp_one_iff_integrable.mp ((Lp.memLp _).mono_exponent (by norm_num : (1:ℝ≥0∞) ≤ 2))

/-- The recorded velocity is related to the curve by the Bochner primitive
identity at every time; it is not a free unrelated third component. -/
theorem circle_parabolic_integral_identity (u : CircleParabolicSpace T τ) (t : unitInterval) :
    circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ u t)-
        circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ u 0) =
      τ • (∫ r in Iic t, circleParabolicTimeDerivative T τ u r ∂volume) :=
  ((circle_parabolic_mem_iff T τ u.1).mp u.property).2 t

end Lemniscate
