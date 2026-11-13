import LengthGrowth.ActualFlow.SpatialPeriodicity
import LengthGrowth.ActualFlow.PeriodicIntegration

/-! Spatial integrations in the first variation of actual immersed curves.
The variation field is arbitrary and genuinely smooth and periodic. No time
evolution identity is assumed or concluded in this fixed-slice module. -/

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace LengthGrowth.ActualFlow

variable {γ V : ℝ → ℂ} {P : ℝ}

theorem length_spatial_first_variation
    (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0)
    (hp : Function.Periodic γ P) (hV : ContDiff ℝ ∞ V)
    (hVp : Function.Periodic V P) :
    (∫ u in 0..P, inner ℝ (deriv V u) (tangent γ u)) =
      -(∫ u in 0..P, speed γ u * curvature γ u * inner ℝ (V u) (normal γ u)) := by
  calc
    _ = ∫ u in 0..P, inner ℝ (tangent γ u) (deriv V u) := by
      apply intervalIntegral.integral_congr
      intro u _
      exact real_inner_comm _ _
    _ = -(∫ u in 0..P, inner ℝ (deriv (tangent γ) u) (V u)) :=
      periodic_inner_integration_by_parts (tangent_smooth hγ hreg) hV
        (tangent_periodic hγ hp) hVp
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only
      rw [(tangent_hasDerivAt hγ hreg u).deriv, ← Complex.real_smul,
        real_inner_smul_left, real_inner_comm (normal γ u) (V u)]

theorem stress_spatial_first_variation
    (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0)
    (hp : Function.Periodic γ P) (hV : ContDiff ℝ ∞ V)
    (hVp : Function.Periodic V P) :
    -(∫ u in 0..P, inner ℝ (stress γ u) (deriv V u)) =
      ∫ u in 0..P, speed γ u * force γ u * inner ℝ (normal γ u) (V u) := by
  rw [periodic_inner_integration_by_parts (stress_smooth hγ hreg) hV
    (stress_periodic hγ hreg hp) hVp, neg_neg]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [(stress_hasDerivAt hγ hreg u).deriv, ← Complex.real_smul, real_inner_smul_left]

theorem stress_inner_actual_velocity_derivative
    (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) :
    inner ℝ (stress γ u) (deriv V u) =
      deriv (curvature γ) u * inner ℝ (arcDerivative γ V u) (normal γ u) +
      curvature γ u ^ 2 / 2 * inner ℝ (deriv V u) (tangent γ u) := by
  have hs : stress γ u = (curvature γ u ^ 2 / 2) • tangent γ u +
      curvatureGradient γ u • normal γ u := by
    simp only [stress, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_ofNat]
  rw [hs, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    (curvature_hasDerivAt hγ hreg u).deriv, arcDerivative, real_inner_smul_left]
  rw [real_inner_comm (tangent γ u) (deriv V u),
    real_inner_comm (normal γ u) (deriv V u)]
  field_simp [(speed_pos hreg u).ne']
  ring

theorem energy_spatial_first_variation
    (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0)
    (hp : Function.Periodic γ P) (hV : ContDiff ℝ ∞ V)
    (hVp : Function.Periodic V P) :
    (∫ u in 0..P, curvature γ u *
        deriv (fun x => inner ℝ (arcDerivative γ V x) (normal γ x)) u -
        curvature γ u ^ 2 / 2 * inner ℝ (deriv V u) (tangent γ u)) =
      ∫ u in 0..P, speed γ u * force γ u * inner ℝ (normal γ u) (V u) := by
  let b : ℝ → ℝ := fun u => inner ℝ (arcDerivative γ V u) (normal γ u)
  have hb : ContDiff ℝ ∞ b :=
    (arcDerivative_smooth hγ hreg hV).inner ℝ (normal_smooth hγ hreg)
  have hbp : Function.Periodic b P := by
    have hd := arcDerivative_periodic hγ hp (hV.differentiable (by simp)) hVp
    have hn := normal_periodic hγ hp
    intro u
    dsimp [b]
    rw [hd u, hn u]
  have hk := curvature_smooth hγ hreg
  have hkd := (contDiff_infty_iff_deriv.mp hk).2.continuous
  have hbd := (contDiff_infty_iff_deriv.mp hb).2.continuous
  have hVd := (contDiff_infty_iff_deriv.mp hV).2.continuous
  have hT := (tangent_smooth hγ hreg).continuous
  have hi₁ : IntervalIntegrable (fun u => curvature γ u * deriv b u) volume 0 P :=
    (hk.continuous.mul hbd).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable
      (fun u => curvature γ u ^ 2 / 2 * inner ℝ (deriv V u) (tangent γ u)) volume 0 P :=
    (((hk.continuous.pow 2).div_const 2).mul (hVd.inner hT)).intervalIntegrable _ _
  have hi₃ : IntervalIntegrable (fun u => deriv (curvature γ) u * b u) volume 0 P :=
    (hkd.mul hb.continuous).intervalIntegrable _ _
  change (∫ u in 0..P, curvature γ u * deriv b u -
    curvature γ u ^ 2 / 2 * inner ℝ (deriv V u) (tangent γ u)) = _
  rw [intervalIntegral.integral_sub hi₁ hi₂,
    periodic_mul_integration_by_parts hk hb (curvature_periodic hγ hreg hp) hbp]
  calc
    _ = -(∫ u in 0..P, deriv (curvature γ) u * b u +
        curvature γ u ^ 2 / 2 * inner ℝ (deriv V u) (tangent γ u)) := by
      rw [intervalIntegral.integral_add hi₃ hi₂]
      ring
    _ = -(∫ u in 0..P, inner ℝ (stress γ u) (deriv V u)) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro u _
      exact (stress_inner_actual_velocity_derivative hγ hreg u).symm
    _ = _ := stress_spatial_first_variation hγ hreg hp hV hVp

end LengthGrowth.ActualFlow

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for n in #[`LengthGrowth.ActualFlow.length_spatial_first_variation,
      `LengthGrowth.ActualFlow.stress_spatial_first_variation,
      `LengthGrowth.ActualFlow.stress_inner_actual_velocity_derivative,
      `LengthGrowth.ActualFlow.energy_spatial_first_variation] do
    for a in (← collectAxioms n) do
      unless allowed.contains a do throwError "Unexpected axiom {a} in {n}"
  logInfo "Actual spatial first variation: standard axioms only."
