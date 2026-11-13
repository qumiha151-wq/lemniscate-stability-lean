import LengthGrowth.ActualFlow.IntrinsicCurve
import LengthGrowth.CurveFromPosition

/-! Actual geometric transport under a coordinate with the arclength inverse
derivative. The derivative premise of these auxiliary lemmas is discharged
by the constructed global inverse in ArclengthSmooth. No unit speed, frame,
curvature, or force transport identity is supplied as a premise.
The legacy bridge at the end compares the two actual derivative definitions.
-/

noncomputable section
open scoped ComplexConjugate ContDiff

namespace LengthGrowth.ActualFlow

section InverseDerivative

variable {γ : ℝ → ℂ} {η : ℝ → ℝ}
variable (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0)
variable (hη : ContDiff ℝ ∞ η)
variable (hηd : ∀ s, HasDerivAt η (speed γ (η s))⁻¹ s)

include hηd in
theorem deriv_comp_arclength_inverse {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} (hf : Differentiable ℝ f) (s : ℝ) :
    deriv (fun x => f (η x)) s = arcDerivative γ f (η s) := by
  exact ((hf (η s)).hasDerivAt.scomp s (hηd s)).deriv

include hγ hηd in
theorem inverse_comp_position_hasDerivAt (s : ℝ) :
    HasDerivAt (fun x => γ (η x)) (tangent γ (η s)) s := by
  exact (hγ.differentiable (by simp) (η s)).hasDerivAt.scomp s (hηd s)

include hγ hreg hηd in
theorem inverse_comp_position_unit (s : ℝ) :
    ‖deriv (fun x => γ (η x)) s‖ = 1 := by
  rw [(inverse_comp_position_hasDerivAt hγ hηd s).deriv]
  exact tangent_unit hreg (η s)

include hγ hreg hηd in
theorem inverse_comp_position_regular (s : ℝ) :
    deriv (fun x => γ (η x)) s ≠ 0 := by
  have hu := inverse_comp_position_unit hγ hreg hηd s
  intro hz
  rw [hz, norm_zero] at hu
  norm_num at hu

include hγ hreg hηd in
theorem inverse_comp_speed (s : ℝ) :
    speed (fun x => γ (η x)) s = 1 :=
  inverse_comp_position_unit hγ hreg hηd s

include hγ hreg hηd in
theorem inverse_comp_tangent (s : ℝ) :
    tangent (fun x => γ (η x)) s = tangent γ (η s) := by
  simp only [tangent, arcDerivative, inverse_comp_speed hγ hreg hηd,
    inv_one, one_smul]
  exact (inverse_comp_position_hasDerivAt hγ hηd s).deriv

include hγ hreg hηd in
theorem inverse_comp_normal (s : ℝ) :
    normal (fun x => γ (η x)) s = normal γ (η s) := by
  simp only [normal, inverse_comp_tangent hγ hreg hηd]

include hγ hreg hη hηd in
theorem inverse_comp_curvature (s : ℝ) :
    curvature (fun x => γ (η x)) s = curvature γ (η s) := by
  have ht : tangent (fun x => γ (η x)) = (fun x => tangent γ (η x)) :=
    funext (inverse_comp_tangent hγ hreg hηd)
  rw [curvature_eq_inner_arcDerivative (γ := fun x => γ (η x)) (hγ.comp hη)
    (inverse_comp_position_regular (γ := γ) (η := η) hγ hreg hηd),
    inverse_comp_normal hγ hreg hηd]
  rw [arcDerivative, inverse_comp_speed hγ hreg hηd, inv_one, one_smul, ht]
  rw [deriv_comp_arclength_inverse hηd
    ((tangent_smooth hγ hreg).differentiable (by simp))]
  exact (curvature_eq_inner_arcDerivative hγ hreg (η s)).symm

include hγ hreg hη hηd in
theorem inverse_comp_curvatureGradient (s : ℝ) :
    curvatureGradient (fun x => γ (η x)) s = curvatureGradient γ (η s) := by
  have hk : curvature (fun x => γ (η x)) = (fun x => curvature γ (η x)) :=
    funext (inverse_comp_curvature hγ hreg hη hηd)
  rw [curvatureGradient, arcDerivative, inverse_comp_speed hγ hreg hηd,
    inv_one, one_smul, hk]
  exact deriv_comp_arclength_inverse hηd
    ((curvature_smooth hγ hreg).differentiable (by simp)) s

include hγ hreg hη hηd in
theorem inverse_comp_curvatureSecond (s : ℝ) :
    curvatureSecond (fun x => γ (η x)) s = curvatureSecond γ (η s) := by
  have hk : curvatureGradient (fun x => γ (η x)) =
      (fun x => curvatureGradient γ (η x)) :=
    funext (inverse_comp_curvatureGradient hγ hreg hη hηd)
  rw [curvatureSecond, arcDerivative, inverse_comp_speed hγ hreg hηd,
    inv_one, one_smul, hk]
  exact deriv_comp_arclength_inverse hηd
    ((curvatureGradient_smooth hγ hreg).differentiable (by simp)) s

include hγ hreg hη hηd in
theorem inverse_comp_force (s : ℝ) :
    force (fun x => γ (η x)) s = force γ (η s) := by
  simp only [force, inverse_comp_curvatureSecond hγ hreg hη hηd,
    inverse_comp_curvature hγ hreg hη hηd]

end InverseDerivative

section LegacyUnitSpeed

variable {β : ℝ → ℂ} (hu : ∀ s, ‖deriv β s‖ = 1)
include hu

theorem unit_speed_actual_tangent : tangent β = deriv β := by
  funext s
  simp only [tangent, arcDerivative, speed, hu s, inv_one, one_smul]

theorem legacy_curvature_eq_actual (s : ℝ) :
    LengthGrowth.positionCurvature β s = curvature β s := by
  simp only [curvature, unit_speed_actual_tangent hu, speed, hu s, div_one,
    LengthGrowth.positionCurvature]

theorem unit_speed_curvatureGradient (s : ℝ) :
    curvatureGradient β s = deriv (curvature β) s := by
  simp only [curvatureGradient, arcDerivative, speed, hu s, inv_one, one_smul]

theorem unit_speed_curvatureSecond (s : ℝ) :
    curvatureSecond β s = deriv (deriv (curvature β)) s := by
  have he : curvatureGradient β = deriv (curvature β) :=
    funext (unit_speed_curvatureGradient hu)
  simp only [curvatureSecond, arcDerivative, speed, hu s, inv_one, one_smul, he]

theorem legacy_force_eq_actual (s : ℝ) :
    deriv (deriv (LengthGrowth.positionCurvature β)) s +
      LengthGrowth.positionCurvature β s ^ 3 / 2 = force β s := by
  have he : LengthGrowth.positionCurvature β = curvature β :=
    funext (legacy_curvature_eq_actual hu)
  rw [he, force, unit_speed_curvatureSecond hu]

end LegacyUnitSpeed
end LengthGrowth.ActualFlow

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (n, _) in (← getEnv).constants do
    if (`LengthGrowth).isPrefixOf n then
      for a in (← collectAxioms n) do
        unless allowed.contains a do throwError "Unexpected axiom {a} in {n}"
      count := count + 1
  logInfo m!"Actual arclength transport: {count} declarations, standard axioms only."
