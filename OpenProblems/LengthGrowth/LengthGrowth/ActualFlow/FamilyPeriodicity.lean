import LengthGrowth.ActualFlow.SpatialPeriodicity
import LengthGrowth.ActualFlow.FamilyRegularity

/-!
# Periodicity of the actual velocity and variation boundary terms

Time differentiation preserves spatial periodicity because the two position
functions agree on a time neighbourhood. In particular velocity periodicity is
derived from position periodicity; it is not a field of the moving immersion.
All statements are at interior times of its open time domain.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace LengthGrowth.ActualFlow

/-- Equality of the position at a spatial period on nearby times also identifies
the actual time derivatives. This statement does not assume a derivative value. -/
theorem time_derivative_periodic_of_eventually
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Γ : ℝ → ℝ → E} {t P : ℝ}
    (hp : ∀ᶠ τ in 𝓝 t, Function.Periodic (Γ τ) P) :
    Function.Periodic (fun u => deriv (fun τ => Γ τ u) t) P := by
  intro u
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hp] with τ hτ
  exact hτ u

theorem time_derivative_periodic_of_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Set ℝ} {Γ : ℝ → ℝ → E} {t P : ℝ}
    (hI : IsOpen I) (hp : ∀ τ ∈ I, Function.Periodic (Γ τ) P) (ht : t ∈ I) :
    Function.Periodic (fun u => deriv (fun τ => Γ τ u) t) P := by
  apply time_derivative_periodic_of_eventually
  filter_upwards [hI.mem_nhds ht] with τ hτ
  exact hp τ hτ

namespace SmoothPeriodicImmersion

variable {I : Set ℝ} (c : SmoothPeriodicImmersion I) {t : ℝ}

theorem velocity_periodic (ht : t ∈ I) :
    Function.Periodic (c.velocity t) c.period :=
  time_derivative_periodic_of_open c.time_open c.periodic ht

theorem arcVelocity_periodic (ht : t ∈ I) :
    Function.Periodic (arcDerivative (c.position t) (c.velocity t)) c.period :=
  arcDerivative_periodic (c.position_slice_smooth ht) (c.periodic t ht)
    ((c.velocity_slice_smooth ht).differentiable (by simp)) (c.velocity_periodic ht)

theorem velocityGradientTangent_periodic (ht : t ∈ I) :
    Function.Periodic (c.velocityGradientTangent t) c.period := by
  have hv := c.arcVelocity_periodic ht
  have hT := tangent_periodic (c.position_slice_smooth ht) (c.periodic t ht)
  intro u
  simp only [velocityGradientTangent, hv u, hT u]

theorem velocityGradientNormal_periodic (ht : t ∈ I) :
    Function.Periodic (c.velocityGradientNormal t) c.period := by
  have hv := c.arcVelocity_periodic ht
  have hN := normal_periodic (c.position_slice_smooth ht) (c.periodic t ht)
  intro u
  simp only [velocityGradientNormal, hv u, hN u]

/-- The first scalar boundary term in the energy variation. -/
theorem curvature_mul_velocityGradientNormal_periodic (ht : t ∈ I) :
    Function.Periodic
      (fun u => curvature (c.position t) u * c.velocityGradientNormal t u) c.period := by
  have hk := curvature_periodic (c.position_slice_smooth ht) (c.immersion t ht)
    (c.periodic t ht)
  have hb := c.velocityGradientNormal_periodic ht
  intro u
  simp only [hk u, hb u]

/-- The stress--velocity boundary term in the energy variation. -/
theorem stress_inner_velocity_periodic (ht : t ∈ I) :
    Function.Periodic
      (fun u => inner ℝ (stress (c.position t) u) (c.velocity t u)) c.period := by
  have hW := stress_periodic (c.position_slice_smooth ht) (c.immersion t ht)
    (c.periodic t ht)
  have hV := c.velocity_periodic ht
  intro u
  simp only [hW u, hV u]

/-- The velocity--tangent boundary term in the length variation. -/
theorem velocity_inner_tangent_periodic (ht : t ∈ I) :
    Function.Periodic
      (fun u => inner ℝ (c.velocity t u) (tangent (c.position t) u)) c.period := by
  have hV := c.velocity_periodic ht
  have hT := tangent_periodic (c.position_slice_smooth ht) (c.periodic t ht)
  intro u
  simp only [hV u, hT u]

theorem variation_boundary_terms_at_period (ht : t ∈ I) :
    (curvature (c.position t) c.period * c.velocityGradientNormal t c.period =
      curvature (c.position t) 0 * c.velocityGradientNormal t 0) ∧
    (inner ℝ (stress (c.position t) c.period) (c.velocity t c.period) =
      inner ℝ (stress (c.position t) 0) (c.velocity t 0)) ∧
    (inner ℝ (c.velocity t c.period) (tangent (c.position t) c.period) =
      inner ℝ (c.velocity t 0) (tangent (c.position t) 0)) := by
  exact ⟨by simpa only [zero_add] using c.curvature_mul_velocityGradientNormal_periodic ht 0,
    by simpa only [zero_add] using c.stress_inner_velocity_periodic ht 0,
    by simpa only [zero_add] using c.velocity_inner_tangent_periodic ht 0⟩

end SmoothPeriodicImmersion
end LengthGrowth.ActualFlow

#print axioms LengthGrowth.ActualFlow.SmoothPeriodicImmersion.velocity_periodic
#print axioms LengthGrowth.ActualFlow.SmoothPeriodicImmersion.variation_boundary_terms_at_period

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`LengthGrowth.ActualFlow).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Family periodicity audit failed: {name} depends on {axiomName}"
      count := count + 1
  logInfo m!"ACTUAL_FAMILY_PERIODICITY_AUDIT {count}: standard three axioms only."
