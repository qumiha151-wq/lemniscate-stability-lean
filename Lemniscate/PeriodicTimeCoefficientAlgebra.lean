import Lemniscate.PeriodicParabolicSpace
import Lemniscate.PeriodicCoefficientAlgebra
import Lemniscate.NormalGraphLowSobolevCoordinates
import Mathlib.Topology.ContinuousMap.Algebra

/-! Continuous coefficients on time times the circle act bilinearly on the
actual time-L2 space. The low normal-graph coordinates are bounded linear
maps from the same complete parabolic space into that coefficient algebra.
Only currying, existing coefficient multiplication and the existing H2
continuous representatives are used here. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter
open scoped ENNReal

variable (T : ℝ) [Fact (0 < T)]

abbrev CircleTimeCoefficient := C(unitInterval × AddCircle T, ℂ)

private def timeCoefficientCurry :
    CircleTimeCoefficient T →L[ℂ] C(unitInterval,C(AddCircle T, ℂ)) where
  toFun := ContinuousMap.curry
  map_add' a b := by
    apply ContinuousMap.ext
    intro t
    apply ContinuousMap.ext
    intro x
    rfl
  map_smul' c a := by
    apply ContinuousMap.ext
    intro t
    apply ContinuousMap.ext
    intro x
    rfl
  cont := ContinuousMap.continuous_curry

private def timeCoefficientUncurry :
    C(unitInterval,C(AddCircle T, ℂ)) →L[ℂ] CircleTimeCoefficient T where
  toFun := ContinuousMap.uncurry
  map_add' a b := by
    apply ContinuousMap.ext
    intro z
    rfl
  map_smul' c a := by
    apply ContinuousMap.ext
    intro z
    rfl
  cont := ContinuousMap.continuous_uncurry

local instance timeCoefficientSecondCountable :
    SecondCountableTopologyEither unitInterval C(AddCircle T, ℂ) where
  out := Or.inl (inferInstance : SecondCountableTopology unitInterval)

/-- Multiplication by a continuous time-dependent circle coefficient,
bundled jointly as a genuine bounded bilinear map. -/
def circleTimeCoefficientMultiplyL2 :
    CircleTimeCoefficient T →L[ℂ] CircleTimeL2 T →L[ℂ] CircleTimeL2 T :=
  ((circleCoefficientMultiplyL2 T).holderL (volume : Measure unitInterval) ∞ 2 2).comp
    ((ContinuousMap.toLp ∞ (volume : Measure unitInterval) ℂ).comp (timeCoefficientCurry T))

private theorem time_coefficient_multiply_ae
    (a : CircleTimeCoefficient T) (w : CircleTimeL2 T) :
    (circleTimeCoefficientMultiplyL2 T a w : unitInterval → CircleL2 T) =ᵐ[volume]
      fun t => circleMultiplyL2 T (a.curry t) (w t) := by
  let A := ContinuousMap.toLp ∞ (volume : Measure unitInterval) ℂ a.curry
  have hm := (circleCoefficientMultiplyL2 T).coeFn_holder (r := 2) A w
  have ha := ContinuousMap.coeFn_toLp (p := ∞)
    (volume : Measure unitInterval) (𝕜 := ℂ) a.curry
  filter_upwards [hm,ha] with t ht hat
  change ((circleCoefficientMultiplyL2 T).holder 2 A w) t =
    circleMultiplyL2 T (a.curry t) (w t)
  rw [ht,hat]
  rfl

/-- The product has its actual pointwise meaning almost everywhere in each
of the two variables; no product-measure identification is needed. -/
theorem circle_time_coefficient_multiply_l2_ae
    (a : CircleTimeCoefficient T) (w : CircleTimeL2 T) :
    ∀ᵐ t : unitInterval ∂volume, ∀ᵐ x : AddCircle T ∂AddCircle.haarAddCircle,
      (circleTimeCoefficientMultiplyL2 T a w t) x = a (t,x)*(w t) x := by
  filter_upwards [time_coefficient_multiply_ae T a w] with t ht
  rw [ht]
  exact circle_multiply_l2_ae T (a.curry t) (w t)

theorem circle_time_coefficient_multiply_l2_norm_le
    (a : CircleTimeCoefficient T) (w : CircleTimeL2 T) :
    ‖circleTimeCoefficientMultiplyL2 T a w‖ ≤ ‖a‖*‖w‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [time_coefficient_multiply_ae T a w] with t ht
  rw [ht]
  have ha : ‖a.curry t‖ ≤ ‖a‖ :=
    (ContinuousMap.norm_le _ (norm_nonneg a)).mpr (fun x => a.norm_coe_le_norm (t,x))
  exact (circle_multiply_l2_norm_le T (a.curry t) (w t)).trans
    (mul_le_mul_of_nonneg_right ha (norm_nonneg _))

/-- The actual [h,sqrt(2)*h_x] coordinates, continuous jointly in time and
space and bounded linearly by the complete parabolic norm. -/
def circleParabolicLowCoordinates (τ : ℝ) :
    CircleParabolicSpace T τ →L[ℂ] (Fin 2 → CircleTimeCoefficient T) :=
  ContinuousLinearMap.pi fun j =>
    let D := (ContinuousLinearMap.proj j).comp (circleNormalGraphLowCoordinates T)
    (timeCoefficientUncurry T).comp
      ((D.compLeftContinuous ℂ unitInterval).comp (circleParabolicCurve T τ))

theorem circle_parabolic_low_coordinates_apply (τ : ℝ)
    (U : CircleParabolicSpace T τ) (j : Fin 2) (t : unitInterval) (x : AddCircle T) :
    circleParabolicLowCoordinates T τ U j (t,x) =
      circleNormalGraphLowCoordinates T (circleParabolicCurve T τ U t) j x := rfl

end Lemniscate
