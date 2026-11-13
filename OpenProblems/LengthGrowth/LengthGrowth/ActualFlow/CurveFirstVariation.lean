import LengthGrowth.ActualFlow.FamilyIntegrals
import LengthGrowth.ActualFlow.FamilyDerivatives
import LengthGrowth.ActualFlow.FamilyPeriodicity
import LengthGrowth.ActualFlow.SpatialFirstVariation
import LengthGrowth.ScalarDissipation

/-! Actual first variations of a smooth periodic family and its normal FEF
specialization. Metric and curvature variation are proved from position in
FamilyDerivatives; the only PDE hypothesis here is the actual normal velocity.
This is an open-time theorem, not an initial-time extension theorem. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth.ActualFlow.SmoothPeriodicImmersion

variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem length_hasDerivAt_firstVariation {t : ℝ} (ht : t ∈ I) :
    HasDerivAt c.length
      (-(∫ u in 0..c.period, speed (c.position t) u * curvature (c.position t) u *
        inner ℝ (c.velocity t u) (normal (c.position t) u))) t := by
  have h := c.length_hasDerivAt_actualTimeDerivative ht
  have he : (∫ u in 0..c.period, deriv (fun x => speed (c.position x) u) t) =
      -(∫ u in 0..c.period, speed (c.position t) u * curvature (c.position t) u *
        inner ℝ (c.velocity t u) (normal (c.position t) u)) := by
    calc
      _ = ∫ u in 0..c.period, inner ℝ (deriv (c.velocity t) u) (tangent (c.position t) u) := by
        apply intervalIntegral.integral_congr
        intro u _
        dsimp only
        rw [(c.speed_time_hasDerivAt ht u).deriv, c.speed_mul_velocityGradientTangent ht u]
      _ = _ := length_spatial_first_variation (c.position_slice_smooth ht)
        (c.immersion t ht) (c.periodic t ht) (c.velocity_slice_smooth ht) (c.velocity_periodic ht)
  rw [he] at h
  exact h

theorem energy_hasDerivAt_firstVariation {t : ℝ} (ht : t ∈ I) :
    HasDerivAt c.energy
      (∫ u in 0..c.period, speed (c.position t) u * force (c.position t) u *
        inner ℝ (normal (c.position t) u) (c.velocity t u)) t := by
  have h := c.energy_hasDerivAt_actualTimeDerivative ht
  have he : ((1 / 2 : ℝ) * ∫ u in 0..c.period,
      deriv (fun x => curvature (c.position x) u ^ 2 * speed (c.position x) u) t) =
      ∫ u in 0..c.period, curvature (c.position t) u * deriv (c.velocityGradientNormal t) u -
        curvature (c.position t) u ^ 2 / 2 *
          inner ℝ (deriv (c.velocity t) u) (tangent (c.position t) u) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    have hk := joint_smooth_time_hasDerivAt c.time_open
      (f := fun x => curvature (c.position x)) c.curvature_joint_smooth ht u
    have hd := (hk.pow 2).mul (c.speed_time_hasDerivAt ht u)
    change HasDerivAt
      (fun x => curvature (c.position x) u ^ 2 * speed (c.position x) u) _ t at hd
    norm_num only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one] at hd
    rw [hd.deriv, ← c.speed_mul_velocityGradientTangent ht u]
    have hm := c.curvature_metric_rate_identity ht u
    linear_combination (curvature (c.position t) u) * hm
  rw [he] at h
  have hs := energy_spatial_first_variation (c.position_slice_smooth ht)
    (c.immersion t ht) (c.periodic t ht) (c.velocity_slice_smooth ht) (c.velocity_periodic ht)
  change (∫ u in 0..c.period, curvature (c.position t) u * deriv (c.velocityGradientNormal t) u -
    curvature (c.position t) u ^ 2 / 2 *
      inner ℝ (deriv (c.velocity t) u) (tangent (c.position t) u)) = _ at hs
  rw [hs] at h
  exact h

/-- Actual vector-valued normal FEF, expressed as a position time derivative. -/
def IsNormalFEF : Prop :=
  ∀ t ∈ I, ∀ u, HasDerivAt (fun x => c.position x u)
    (-(force (c.position t) u : ℂ) * normal (c.position t) u) t

theorem normal_velocity_eq (hflow : c.IsNormalFEF) {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    c.velocity t u = -(force (c.position t) u : ℂ) * normal (c.position t) u :=
  (c.position_time_hasDerivAt ht u).unique (hflow t ht u)

theorem normal_inner_velocity (hflow : c.IsNormalFEF) {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    inner ℝ (normal (c.position t) u) (c.velocity t u) = -force (c.position t) u := by
  rw [c.normal_velocity_eq hflow ht u]
  rw [show -(force (c.position t) u : ℂ) * normal (c.position t) u =
    (-force (c.position t) u) • normal (c.position t) u by
      simp only [Complex.real_smul, Complex.ofReal_neg]]
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq, normal_unit (c.immersion t ht)]
  ring

theorem length_hasDerivAt_normal (hflow : c.IsNormalFEF) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt c.length (c.lengthRate t) t := by
  have h := c.length_hasDerivAt_firstVariation ht
  have he : -(∫ u in 0..c.period, speed (c.position t) u * curvature (c.position t) u *
        inner ℝ (c.velocity t u) (normal (c.position t) u)) = c.lengthRate t := by
    change _ = ∫ u in 0..c.period,
      curvature (c.position t) u * force (c.position t) u * speed (c.position t) u
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    rw [← real_inner_comm (c.velocity t u) (normal (c.position t) u),
      c.normal_inner_velocity hflow ht u]
    ring
  rw [he] at h
  exact h

theorem energy_hasDerivAt_normal (hflow : c.IsNormalFEF) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt c.energy (-c.dissipation t) t := by
  have h := c.energy_hasDerivAt_firstVariation ht
  have he : (∫ u in 0..c.period, speed (c.position t) u * force (c.position t) u *
        inner ℝ (normal (c.position t) u) (c.velocity t u)) = -c.dissipation t := by
    change _ = -(∫ u in 0..c.period, force (c.position t) u ^ 2 * speed (c.position t) u)
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    rw [c.normal_inner_velocity hflow ht u]
    ring
  rw [he] at h
  exact h

theorem energy_sq_hasDerivAt_normal (hflow : c.IsNormalFEF) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun x => c.energy x ^ 2) (-(2 * c.energy t * c.dissipation t)) t := by
  have h := (c.energy_hasDerivAt_normal hflow ht).pow 2
  change HasDerivAt (fun x => c.energy x ^ 2) _ t at h
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_neg] at h
  exact h

/-- The scalar restart estimate now has actual position-defined L and E. -/
theorem actual_secant_sq_le_energy_drop (hflow : c.IsNormalFEF) {s t : ℝ}
    (hst : s < t) (hsub : Icc s t ⊆ I) :
    (c.length t - c.length s) ^ 2 ≤
      (t - s) * (c.energy s ^ 2 - c.energy t ^ 2) := by
  apply FreeElasticScalar.secant_sq_le_energy_drop c.length (fun x => c.energy x ^ 2)
    c.lengthRate (fun x => -(2 * c.energy x * c.dissipation x)) s t hst
    (c.length_continuousOn.mono hsub) ((c.energy_continuousOn.pow 2).mono hsub)
  · intro x hx
    exact c.length_hasDerivAt_normal hflow (hsub ⟨hx.1.le, hx.2.le⟩)
  · intro x hx
    exact c.energy_sq_hasDerivAt_normal hflow (hsub ⟨hx.1.le, hx.2.le⟩)
  · intro x hx
    simpa only [neg_neg] using c.lengthRate_sq_le (hsub ⟨hx.1.le, hx.2.le⟩)

end LengthGrowth.ActualFlow.SmoothPeriodicImmersion

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (n, _) in (← getEnv).constants do
    if (`LengthGrowth.ActualFlow).isPrefixOf n then
      for a in (← collectAxioms n) do
        unless allowed.contains a do throwError "Unexpected axiom {a} in {n}"
      count := count + 1
  logInfo m!"Actual open-time first variation: {count} declarations, standard axioms only."
