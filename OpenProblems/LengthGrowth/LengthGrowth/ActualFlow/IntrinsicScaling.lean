import LengthGrowth.ActualFlow.MaterialIntegrals
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Positive spatial dilation of actual intrinsic fields. Every identity
is derived from the position and actual deriv operators. The force scaling
is a conclusion, not an independent assumption. Field-valued derivative
linearity makes these algebraic identities valid even before regularity
is imposed on a curve. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate ContDiff
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth.ActualFlow

def scalePosition (r : ℝ) (γ : ℝ → ℂ) (u : ℝ) : ℂ := r • γ u

theorem scalePosition_deriv (r : ℝ) (γ : ℝ → ℂ) (u : ℝ) :
    deriv (scalePosition r γ) u = r • deriv γ u :=
  deriv_fun_const_smul_field r γ

theorem scalePosition_iteratedDeriv (r : ℝ) (γ : ℝ → ℂ) (j : ℕ) (u : ℝ) :
    iteratedDeriv j (scalePosition r γ) u = r • iteratedDeriv j γ u :=
  iteratedDeriv_fun_const_smul_field r γ

theorem scalePosition_smooth (r : ℝ) {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) :
    ContDiff ℝ ∞ (scalePosition r γ) := hγ.const_smul r

theorem scalePosition_regular {r : ℝ} (hr : 0 < r) {γ : ℝ → ℂ}
    (hreg : ∀ u, deriv γ u ≠ 0) (u : ℝ) : deriv (scalePosition r γ) u ≠ 0 := by
  rw [scalePosition_deriv]
  exact smul_ne_zero (ne_of_gt hr) (hreg u)

theorem scalePosition_periodic (r : ℝ) {γ : ℝ → ℂ} {P : ℝ}
    (hp : Function.Periodic γ P) : Function.Periodic (scalePosition r γ) P := by
  intro u
  exact congrArg (fun z : ℂ => r • z) (hp u)

theorem scalePosition_speed {r : ℝ} (hr : 0 < r) (γ : ℝ → ℂ) (u : ℝ) :
    speed (scalePosition r γ) u = r * speed γ u := by
  simp only [speed, scalePosition_deriv, norm_smul, Real.norm_eq_abs, abs_of_pos hr]

theorem scalePosition_arcDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (hr : 0 < r) (γ : ℝ → ℂ) (f : ℝ → E) (u : ℝ) :
    arcDerivative (scalePosition r γ) f u = r⁻¹ • arcDerivative γ f u := by
  simp only [arcDerivative, scalePosition_speed hr, mul_inv, smul_smul]

theorem scalePosition_tangent {r : ℝ} (hr : 0 < r) (γ : ℝ → ℂ) (u : ℝ) :
    tangent (scalePosition r γ) u = tangent γ u := by
  simp only [tangent, arcDerivative, scalePosition_speed hr, scalePosition_deriv,
    mul_inv, smul_smul]
  congr 1
  field_simp [ne_of_gt hr]

theorem scalePosition_normal {r : ℝ} (hr : 0 < r) (γ : ℝ → ℂ) (u : ℝ) :
    normal (scalePosition r γ) u = normal γ u := by
  simp only [normal, scalePosition_tangent hr]

theorem scalePosition_curvature {r : ℝ} (hr : 0 < r) (γ : ℝ → ℂ) (u : ℝ) :
    curvature (scalePosition r γ) u = curvature γ u / r := by
  have ht : tangent (scalePosition r γ) = tangent γ := funext (scalePosition_tangent hr γ)
  simp only [curvature, ht, scalePosition_speed hr, div_eq_mul_inv, mul_inv]
  ring

theorem scalePosition_curvatureGradient {r : ℝ} (hr : 0 < r) (γ : ℝ → ℂ) (u : ℝ) :
    curvatureGradient (scalePosition r γ) u = curvatureGradient γ u / r ^ 2 := by
  have hk : curvature (scalePosition r γ) = (fun x => curvature γ x / r) :=
    funext (scalePosition_curvature hr γ)
  simp only [curvatureGradient, arcDerivative, scalePosition_speed hr, hk, deriv_div_const, smul_eq_mul]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem scalePosition_curvatureSecond {r : ℝ} (hr : 0 < r) (γ : ℝ → ℂ) (u : ℝ) :
    curvatureSecond (scalePosition r γ) u = curvatureSecond γ u / r ^ 3 := by
  have hk : curvatureGradient (scalePosition r γ) =
      (fun x => curvatureGradient γ x / r ^ 2) :=
    funext (scalePosition_curvatureGradient hr γ)
  simp only [curvatureSecond, arcDerivative, scalePosition_speed hr, hk, deriv_div_const, smul_eq_mul]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem scalePosition_force {r : ℝ} (hr : 0 < r) (γ : ℝ → ℂ) (u : ℝ) :
    force (scalePosition r γ) u = force γ u / r ^ 3 := by
  simp only [force, scalePosition_curvatureSecond hr, scalePosition_curvature hr]
  ring

theorem scalePosition_materialLength {r : ℝ} (hr : 0 < r) (γ : ℝ → ℂ) (P : ℝ) :
    materialLength (scalePosition r γ) P = r * materialLength γ P := by
  simp only [materialLength, scalePosition_speed hr, intervalIntegral.integral_const_mul]

theorem scalePosition_materialEnergy {r : ℝ} (hr : 0 < r) (γ : ℝ → ℂ) (P : ℝ) :
    materialEnergy (scalePosition r γ) P = materialEnergy γ P / r := by
  have hi : (fun u => curvature (scalePosition r γ) u ^ 2 * speed (scalePosition r γ) u) =
      (fun u => r⁻¹ * (curvature γ u ^ 2 * speed γ u)) := by
    funext u
    rw [scalePosition_curvature hr, scalePosition_speed hr]
    field_simp [ne_of_gt hr]
  simp only [materialEnergy, hi, intervalIntegral.integral_const_mul]
  ring

theorem scalePosition_materialDissipation {r : ℝ} (hr : 0 < r) (γ : ℝ → ℂ) (P : ℝ) :
    materialDissipation (scalePosition r γ) P = materialDissipation γ P / r ^ 5 := by
  have hi : (fun u => force (scalePosition r γ) u ^ 2 * speed (scalePosition r γ) u) =
      (fun u => (r ^ 5)⁻¹ * (force γ u ^ 2 * speed γ u)) := by
    funext u
    rw [scalePosition_force hr, scalePosition_speed hr]
    field_simp [ne_of_gt hr]
  simp only [materialDissipation, hi, intervalIntegral.integral_const_mul]
  ring

theorem scalePosition_materialLengthRate {r : ℝ} (hr : 0 < r) (γ : ℝ → ℂ) (P : ℝ) :
    materialLengthRate (scalePosition r γ) P = materialLengthRate γ P / r ^ 3 := by
  have hi : (fun u => curvature (scalePosition r γ) u * force (scalePosition r γ) u *
      speed (scalePosition r γ) u) =
      (fun u => (r ^ 3)⁻¹ * (curvature γ u * force γ u * speed γ u)) := by
    funext u
    rw [scalePosition_curvature hr, scalePosition_force hr, scalePosition_speed hr]
    field_simp [ne_of_gt hr]
  simp only [materialLengthRate, hi, intervalIntegral.integral_const_mul]
  ring

end LengthGrowth.ActualFlow

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`LengthGrowth).isPrefixOf name || (`FreeElasticScalar).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext, `Classical.choice, `Quot.sound] : Array Name).contains axiomName do
          throwError "Actual intrinsic scaling audit failed: {name} depends on {axiomName}"
      count := count + 1
  logInfo m!"ACTUAL_INTRINSIC_SCALING_AUDIT {count}: standard three axioms only."
