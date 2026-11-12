import OpenTranslators.ImmersionFrenet
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.LinearCombination

/-! Global angle lifting for actual smooth unit-speed coordinate immersions.
The angle is constructed as the integral of actual signed curvature. The
Frenet equations and identification with the tangent are proved, not assumed. -/

namespace OpenTranslator.ImmersionAngle
noncomputable section
open MeasureTheory Set
open OpenTranslator.Immersion
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

def initialAngle (x y : ℝ → ℝ) : ℝ := Complex.arg ⟨deriv x 0, deriv y 0⟩
def angle (x y : ℝ → ℝ) (s : ℝ) : ℝ := initialAngle x y + ∫ u in 0..s, curvature x y u

variable {x y : ℝ → ℝ}
variable (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
variable (hunit : ∀ s, (deriv x s)^2+(deriv y s)^2=1)

include hunit in
theorem initial_complex_norm : ‖(⟨deriv x 0, deriv y 0⟩ : ℂ)‖ = 1 := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  change Real.sqrt ((deriv x 0)^2+(deriv y 0)^2)=1
  rw [hunit 0, Real.sqrt_one]

include hunit in
theorem initialAngle_cos : Real.cos (initialAngle x y) = deriv x 0 := by
  have hn := initial_complex_norm hunit
  have hne : (⟨deriv x 0, deriv y 0⟩ : ℂ) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    norm_num at hn
  rw [initialAngle, Complex.cos_arg hne, hn, div_one]

include hunit in
theorem initialAngle_sin : Real.sin (initialAngle x y) = deriv y 0 := by
  rw [initialAngle, Complex.sin_arg, initial_complex_norm hunit, div_one]

@[simp] theorem angle_zero : angle x y 0 = initialAngle x y := by simp [angle]

include hx hy in
theorem angle_hasDerivAt (s : ℝ) : HasDerivAt (angle x y) (curvature x y s) s := by
  have hc := (curvature_smooth hx hy).continuous
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add _

include hx hy in
theorem angle_smooth : ContDiff ℝ ∞ (angle x y) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun s => (angle_hasDerivAt hx hy s).differentiableAt, ?_⟩
  have he : deriv (angle x y) = curvature x y := funext fun s => (angle_hasDerivAt hx hy s).deriv
  rw [he]
  exact curvature_smooth hx hy

def augmentedFrenetField (x y : ℝ → ℝ) (u : TranslatorState) : TranslatorState :=
  ![1, -curvature x y (u 0) * u 2, curvature x y (u 0) * u 1]
def actualTangentPath (x y : ℝ → ℝ) (s : ℝ) : TranslatorState := ![s, deriv x s, deriv y s]
def angleTangentPath (x y : ℝ → ℝ) (s : ℝ) : TranslatorState :=
  ![s, Real.cos (angle x y s), Real.sin (angle x y s)]

include hx hy in
theorem augmentedFrenetField_smooth : ContDiff ℝ ∞ (augmentedFrenetField x y) := by
  have hk := curvature_smooth hx hy
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [augmentedFrenetField] <;> fun_prop

include hx hy hunit in
theorem actualTangentPath_hasDerivAt (s : ℝ) :
    HasDerivAt (actualTangentPath x y)
      (augmentedFrenetField x y (actualTangentPath x y s)) s := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_id s
  · change HasDerivAt (deriv x) (-curvature x y s * deriv y s) s
    rw [← frenet_x hx hy hunit s]
    exact ((contDiff_infty_iff_deriv.mp hx).2.differentiable (by simp) s).hasDerivAt
  · change HasDerivAt (deriv y) (curvature x y s * deriv x s) s
    rw [← frenet_y hx hy hunit s]
    exact ((contDiff_infty_iff_deriv.mp hy).2.differentiable (by simp) s).hasDerivAt

include hx hy in
theorem angleTangentPath_hasDerivAt (s : ℝ) :
    HasDerivAt (angleTangentPath x y)
      (augmentedFrenetField x y (angleTangentPath x y s)) s := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_id s
  · change HasDerivAt (fun u => Real.cos (angle x y u))
      (-curvature x y s * Real.sin (angle x y s)) s
    convert (angle_hasDerivAt hx hy s).cos using 1
    ring
  · change HasDerivAt (fun u => Real.sin (angle x y u))
      (curvature x y s * Real.cos (angle x y s)) s
    convert (angle_hasDerivAt hx hy s).sin using 1
    ring

include hx hy hunit in
theorem actual_tangent_eq_angle_path : actualTangentPath x y = angleTangentPath x y := by
  have hC1 : ContDiff ℝ 1 (augmentedFrenetField x y) :=
    (augmentedFrenetField_smooth hx hy).of_le (by simp)
  apply unique_global_of_locallyLipschitz hC1.locallyLipschitz
    (actualTangentPath_hasDerivAt hx hy hunit) (angleTangentPath_hasDerivAt hx hy)
    (t₀ := 0)
  ext i
  fin_cases i <;> simp [actualTangentPath, angleTangentPath,
    initialAngle_cos hunit, initialAngle_sin hunit]

include hx hy hunit in
/-- A global smooth tangent angle is constructed from the actual positions. -/
theorem tangent_angle_identification (s : ℝ) :
    deriv x s = Real.cos (angle x y s) ∧ deriv y s = Real.sin (angle x y s) := by
  have he := congrFun (actual_tangent_eq_angle_path hx hy hunit) s
  exact ⟨congrFun he 1, congrFun he 2⟩

end
end OpenTranslator.ImmersionAngle

#print axioms OpenTranslator.ImmersionAngle.tangent_angle_identification

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`OpenTranslator).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
      checked := checked + 1
  logInfo m!"ImmersionAngle: audited {checked} declarations; standard axioms only."
