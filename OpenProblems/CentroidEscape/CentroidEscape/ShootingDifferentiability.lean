import CentroidEscape.ShootingVariation
import CentroidEscape.MidpointDerivative

/-!
# Genuine initial-state derivatives of the actual shooting flow

The derivative is derived from the already proved actual midpoint estimate
by a convergent dyadic construction. Neither differentiability of the flow
nor a globally smooth clipped field is an input assumption.
-/
namespace CentroidEscape
noncomputable section
open Set Real
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false

theorem shootingFlow_exists_initial_fderiv_near (T : ℝ) (hT : 0 ≤ T)
    {c : WeightedState} (hc : ∀ s ∈ Icc 0 T, shootingFlow T hT s c ∈ innerWeightedTube)
    {a : WeightedState} (ha : dist a c < shootingNeighborhoodRadius T)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∃ A : WeightedState →L[ℝ] WeightedState,
      HasFDerivAt (shootingFlow T hT t) A a ∧ ‖A‖ ≤ exp (8*t) ∧
      ∀ u, ‖u‖ < shootingNeighborhoodRadius T-dist a c →
        ‖shootingFlow T hT t (a+u)-shootingFlow T hT t a-A u‖ ≤
          (11/4:ℝ)*exp (16*t)*‖u‖^2 := by
  have hsub : ∀ p ∈ Metric.ball a (shootingNeighborhoodRadius T-dist a c),
      dist p c < shootingNeighborhoodRadius T := by
    intro p hp
    have hd := dist_triangle p a c
    have hp' : dist p a < shootingNeighborhoodRadius T-dist a c := hp
    linarith
  have hmid : ∀ p ∈ Metric.ball a (shootingNeighborhoodRadius T-dist a c),
      ∀ q ∈ Metric.ball a (shootingNeighborhoodRadius T-dist a c),
      ‖shootingFlow T hT t ((1/2:ℝ) • (p+q))-
        (1/2:ℝ) • (shootingFlow T hT t p+shootingFlow T hT t q)‖ ≤
        ((11/16:ℝ)*exp (16*t))*‖p-q‖^2 := by
    intro p hp q hq
    have hm := shootingFlow_midpoint_quadratic_of_inner T hT hc (hsub p hp) (hsub q hq) t ht
    rw [norm_sub_rev] at hm
    simpa only [stateMidpoint,dist_eq_norm] using hm
  obtain ⟨A,hA,hbound,hrem⟩ := exists_hasFDerivAt_of_quadratic_midpoints
    (shootingFlow_initial_lipschitz T hT ht) (sub_pos.mpr ha)
    (by positivity : (0:ℝ) ≤ (11/16)*exp (16*t)) hmid
  refine ⟨A,hA,hbound,?_⟩
  intro u hu
  convert! hrem u hu using 1
  ring

theorem shootingFlow_hasFDerivAt_initial_near (T : ℝ) (hT : 0 ≤ T)
    {c : WeightedState} (hc : ∀ s ∈ Icc 0 T, shootingFlow T hT s c ∈ innerWeightedTube)
    {a : WeightedState} (ha : dist a c < shootingNeighborhoodRadius T)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasFDerivAt (shootingFlow T hT t) (fderiv ℝ (shootingFlow T hT t) a) a := by
  obtain ⟨A,hA,_,_⟩ := shootingFlow_exists_initial_fderiv_near T hT hc ha ht
  exact hA.differentiableAt.hasFDerivAt

theorem shootingFlow_initial_fderiv_bound (T : ℝ) (hT : 0 ≤ T)
    {c : WeightedState} (hc : ∀ s ∈ Icc 0 T, shootingFlow T hT s c ∈ innerWeightedTube)
    {a : WeightedState} (ha : dist a c < shootingNeighborhoodRadius T)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖fderiv ℝ (shootingFlow T hT t) a‖ ≤ exp (8*t) := by
  obtain ⟨A,hA,hbound,_⟩ := shootingFlow_exists_initial_fderiv_near T hT hc ha ht
  rw [hA.fderiv]
  exact hbound

theorem shootingFlow_initial_quadratic_remainder (T : ℝ) (hT : 0 ≤ T)
    {c : WeightedState} (hc : ∀ s ∈ Icc 0 T, shootingFlow T hT s c ∈ innerWeightedTube)
    {a : WeightedState} (ha : dist a c < shootingNeighborhoodRadius T)
    {t : ℝ} (ht : t ∈ Icc 0 T) {u : WeightedState}
    (hu : ‖u‖ < shootingNeighborhoodRadius T-dist a c) :
    ‖shootingFlow T hT t (a+u)-shootingFlow T hT t a-
      fderiv ℝ (shootingFlow T hT t) a u‖ ≤ (11/4:ℝ)*exp (16*t)*‖u‖^2 := by
  obtain ⟨A,hA,_,hrem⟩ := shootingFlow_exists_initial_fderiv_near T hT hc ha ht
  rw [hA.fderiv]
  exact hrem u hu

/-- Successful concrete grid checks supply all region hypotheses for the
actual initial-state derivative, on a whole explicit open neighborhood. -/
theorem checked_grid_shootingFlow_initial_differentiable
    {S N : ℕ} (hS : 0<S) (hN : 0<N) {h : ℚ} (hh : 0 ≤ h) (hhmax : h ≤ 1/100)
    {b : BallVector} (hc : (computeBallGrid S h b N).checks = true)
    {c : WeightedState} (hc0 : ∀ i, (b i).Contains (c i)) :
    let T : ℝ := (N:ℝ)*(h:ℝ)
    let hT : 0 ≤ T := mul_nonneg (Nat.cast_nonneg N) (Rat.cast_nonneg.mpr hh)
    ∀ a ∈ Metric.ball c (shootingNeighborhoodRadius T), ∀ t ∈ Icc 0 T,
      HasFDerivAt (shootingFlow T hT t) (fderiv ℝ (shootingFlow T hT t) a) a := by
  intro T hT a ha t ht
  exact shootingFlow_hasFDerivAt_initial_near T hT
    (shootingFlow_inner_of_checked_grid hS hN hh hhmax hc hc0) ha ht

end
end CentroidEscape

#print axioms CentroidEscape.shootingFlow_hasFDerivAt_initial_near
#print axioms CentroidEscape.checked_grid_shootingFlow_initial_differentiable

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Shooting-differentiability audit passed for {checked} declarations."
