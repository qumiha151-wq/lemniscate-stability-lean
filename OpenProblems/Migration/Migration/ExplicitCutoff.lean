import Migration.TwoEndpointCost
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! A C¹ half-line cutoff with explicit slope bound and primitive on one half period. -/
noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.StripCutoff

def density (v : ℝ) : ℝ := Real.sin (max v 0)/2
def weight (v : ℝ) : ℝ := ∫ x in 0..v, density x
def primitive (v : ℝ) : ℝ := ∫ x in 0..v, weight x

theorem density_continuous : Continuous density :=
  (Real.continuous_sin.comp (continuous_id.max continuous_const)).div_const 2

theorem weight_hasDerivAt (x : ℝ) : HasDerivAt weight (density x) x :=
  intervalIntegral.integral_hasDerivAt_right (density_continuous.intervalIntegrable _ _)
    density_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter density_continuous.continuousAt

theorem weight_continuous : Continuous weight :=
  continuous_iff_continuousAt.mpr fun x => (weight_hasDerivAt x).continuousAt

theorem primitive_hasDerivAt (x : ℝ) : HasDerivAt primitive (weight x) x :=
  intervalIntegral.integral_hasDerivAt_right (weight_continuous.intervalIntegrable _ _)
    weight_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter weight_continuous.continuousAt

theorem weight_of_nonpos {x : ℝ} (hx : x ≤ 0) : weight x = 0 := by
  unfold weight
  rw [show (∫ u in 0..x, density u) = ∫ _u in 0..x, (0:ℝ) by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_comm, uIcc_of_le hx] at hu
    simp [density,max_eq_right hu.2]]
  simp

theorem weight_of_nonneg {x : ℝ} (hx : 0 ≤ x) : weight x = (1-Real.cos x)/2 := by
  unfold weight
  rw [show (∫ u in 0..x, density u) = ∫ u in 0..x, Real.sin u / 2 by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hx] at hu
    simp only [density,max_eq_left hu.1]]
  rw [intervalIntegral.integral_div,integral_sin,Real.cos_zero]

theorem weight_mem (x : ℝ) : 0 ≤ weight x ∧ weight x ≤ 1 := by
  rcases le_total x 0 with h|h
  · simp [weight_of_nonpos h]
  · rw [weight_of_nonneg h]
    constructor <;> linarith [Real.cos_le_one x, Real.neg_one_le_cos x]

theorem density_abs_le (x : ℝ) : |density x| ≤ Real.sqrt (weight x) := by
  rcases le_total x 0 with h|h
  · simp [density,max_eq_right h,weight_of_nonpos h]
  · have hs := Real.sq_sqrt (weight_mem x).1
    have hsq : (density x)^2 ≤ weight x := by
      rw [weight_of_nonneg h]
      simp only [density, max_eq_left h]
      nlinarith [Real.sin_sq_add_cos_sq x,sq_nonneg (1-Real.cos x)]
    exact (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp (by rwa [sq_abs,hs])

theorem primitive_zero : primitive 0 = 0 := by simp [primitive]

theorem primitive_pi : primitive Real.pi = Real.pi / 2 := by
  unfold primitive
  rw [show (∫ u in 0..Real.pi, weight u) = ∫ u in 0..Real.pi, (1-Real.cos u)/2 by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le Real.pi_pos.le] at hu
    exact weight_of_nonneg hu.1]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub intervalIntegrable_const
    (Real.continuous_cos.intervalIntegrable _ _), integral_cos, Real.sin_pi,Real.sin_zero,
    intervalIntegral.integral_const]
  simp

def scaled (k a : ℝ) (r : ℝ → ℝ) (hr : Continuous r)
    (hcover : ∀ z, 0 < k*(z-a) → r z=1) : HeightCutoff where
  weight z := weight (k*(z-a))
  derivative z := density (k*(z-a))*k
  localization := r
  slope := |k|
  deriv_weight z := by
    have h := (weight_hasDerivAt (k*(z-a))).comp z (((hasDerivAt_id z).sub_const a).const_mul k)
    simpa only [mul_one, Function.comp_def, id_eq] using h
  derivative_continuous := (density_continuous.comp ((continuous_id.sub continuous_const).const_mul k)).mul_const k
  localization_continuous := hr
  slope_nonneg := abs_nonneg _
  weight_nonneg z := (weight_mem _).1
  weight_le_one z := (weight_mem _).2
  gradient_bound z := by
    rw [abs_mul,mul_comm]
    exact mul_le_mul_of_nonneg_left (density_abs_le _) (abs_nonneg _)
  localization_one z hz := hcover z (lt_of_not_ge fun h => hz (weight_of_nonpos h))

theorem scaled_primitive_hasDerivAt {k : ℝ} (hk : k ≠ 0) (a z : ℝ) :
    HasDerivAt (fun h => primitive (k*(h-a))/k) (weight (k*(z-a))) z := by
  have h := ((primitive_hasDerivAt (k*(z-a))).comp z
    (((hasDerivAt_id z).sub_const a).const_mul k)).div_const k
  simpa only [mul_one, mul_div_cancel_right₀ _ hk, Function.comp_def, id_eq] using h

end MigrationGeometry.Flow.StripCutoff
