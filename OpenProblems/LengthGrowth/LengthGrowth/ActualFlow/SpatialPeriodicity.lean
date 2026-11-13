import LengthGrowth.ActualFlow.IntrinsicCurve

/-!
# Spatial periodicity of the actual intrinsic fields

Only periodicity of the position is supplied. The speed, frame, curvature,
arclength derivatives, force, and stress inherit it from their actual
definitions. The actual-derivative proof follows the independent
`LengthGrowth/CurveFromPosition.lean` helper; no other project is imported.
-/

noncomputable section
open scoped ContDiff

namespace LengthGrowth.ActualFlow

theorem actual_deriv_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {P : ℝ} (hp : Function.Periodic f P) (hf : Differentiable ℝ f) :
    Function.Periodic (deriv f) P := by
  intro u
  have hd := (hf (u+P)).hasDerivAt.scomp u ((hasDerivAt_id u).add_const P)
  have he : (fun s => f (s+P)) = f := funext hp
  simp only [one_smul] at hd
  change HasDerivAt (fun s => f (s+P)) (deriv f (u+P)) u at hd
  rw [he] at hd
  exact hd.unique (hf u).hasDerivAt

variable {γ : ℝ → ℂ} {P : ℝ}

theorem speed_periodic (hγ : ContDiff ℝ ∞ γ) (hp : Function.Periodic γ P) :
    Function.Periodic (speed γ) P := by
  have hd := actual_deriv_periodic hp (hγ.differentiable (by simp))
  intro u
  simp only [speed, hd u]

theorem arcDerivative_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hγ : ContDiff ℝ ∞ γ) (hp : Function.Periodic γ P)
    {f : ℝ → E} (hf : Differentiable ℝ f) (hfp : Function.Periodic f P) :
    Function.Periodic (arcDerivative γ f) P := by
  have hg := speed_periodic hγ hp
  have hd := actual_deriv_periodic hfp hf
  intro u
  simp only [arcDerivative, hg u, hd u]

theorem tangent_periodic (hγ : ContDiff ℝ ∞ γ) (hp : Function.Periodic γ P) :
    Function.Periodic (tangent γ) P :=
  arcDerivative_periodic hγ hp (hγ.differentiable (by simp)) hp

theorem normal_periodic (hγ : ContDiff ℝ ∞ γ) (hp : Function.Periodic γ P) :
    Function.Periodic (normal γ) P := by
  have ht := tangent_periodic hγ hp
  intro u
  simp only [normal, ht u]

theorem curvature_periodic (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0)
    (hp : Function.Periodic γ P) : Function.Periodic (curvature γ) P := by
  have ht := tangent_periodic hγ hp
  have hdt := actual_deriv_periodic ht ((tangent_smooth hγ hreg).differentiable (by simp))
  have hg := speed_periodic hγ hp
  intro u
  simp only [curvature, ht u, hdt u, hg u]

theorem curvatureGradient_periodic (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) (hp : Function.Periodic γ P) :
    Function.Periodic (curvatureGradient γ) P :=
  arcDerivative_periodic hγ hp ((curvature_smooth hγ hreg).differentiable (by simp))
    (curvature_periodic hγ hreg hp)

theorem curvatureSecond_periodic (hγ : ContDiff ℝ ∞ γ)
    (hreg : ∀ u, deriv γ u ≠ 0) (hp : Function.Periodic γ P) :
    Function.Periodic (curvatureSecond γ) P :=
  arcDerivative_periodic hγ hp ((curvatureGradient_smooth hγ hreg).differentiable (by simp))
    (curvatureGradient_periodic hγ hreg hp)

theorem force_periodic (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0)
    (hp : Function.Periodic γ P) : Function.Periodic (force γ) P := by
  have hk := curvature_periodic hγ hreg hp
  have hk₂ := curvatureSecond_periodic hγ hreg hp
  intro u
  simp only [force, hk u, hk₂ u]

theorem stress_periodic (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0)
    (hp : Function.Periodic γ P) : Function.Periodic (stress γ) P := by
  have ht := tangent_periodic hγ hp
  have hn := normal_periodic hγ hp
  have hk := curvature_periodic hγ hreg hp
  have hk₁ := curvatureGradient_periodic hγ hreg hp
  intro u
  simp only [stress, ht u, hn u, hk u, hk₁ u]

/-- The actual stress boundary term has matching values at a period. -/
theorem stress_at_period (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u ≠ 0)
    (hp : Function.Periodic γ P) : stress γ P = stress γ 0 := by
  simpa only [zero_add] using stress_periodic hγ hreg hp 0

end LengthGrowth.ActualFlow

#print axioms LengthGrowth.ActualFlow.curvature_periodic
#print axioms LengthGrowth.ActualFlow.force_periodic
#print axioms LengthGrowth.ActualFlow.stress_at_period

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`LengthGrowth.ActualFlow).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Spatial periodicity audit failed: {name} depends on {axiomName}"
      count := count + 1
  logInfo m!"ACTUAL_SPATIAL_PERIODICITY_AUDIT {count}: standard three axioms only."
