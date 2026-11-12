import SolitonClassification.OneSignCurvature

/-!
# Positivity of the dilation coefficient follows from the actual support ODE

No expanding hypothesis is needed in this module. Nontrivial periodic support
profiles automatically have a positive dilation coefficient. Combined with
the one-sign theorem this excludes nonexpanding dilation-rotation profiles
in this periodic support formulation. A separate pure-translation generator
is not represented by these four equations and is not asserted covered here.
-/
namespace ClosedSimilarity
noncomputable section
namespace PeriodicSupportProfile
variable {a b L : ℝ} (z : PeriodicSupportProfile a b L)
include z

theorem bending_pos_of_period (hL : 0 < L) : 0 < z.bending := by
  have hn := z.bending_nonneg hL.le
  have hc := interval_integral_cauchy_sq z.continuous_k z.continuous_p hL.le
  rw [z.integral_kp] at hc
  change (-L)^2 ≤ z.bending * (∫ s in 0..L, (z.p s)^2) at hc
  by_contra hh
  have hz : z.bending = 0 := le_antisymm (le_of_not_gt hh) hn
  rw [hz, zero_mul, neg_sq] at hc
  nlinarith [sq_pos_of_pos hL]

theorem forceSquare_pos_of_period (hL : 0 < L) : 0 < z.forceSquare := by
  have hn : 0 ≤ z.forceSquare :=
    intervalIntegral.integral_nonneg_of_forall hL.le (fun s => sq_nonneg (z.force s))
  have hc := interval_integral_cauchy_sq z.continuous_force z.continuous_p hL.le
  rw [z.integral_force_p] at hc
  change (-z.bending/2)^2 ≤ z.forceSquare * (∫ s in 0..L, (z.p s)^2) at hc
  by_contra hh
  have hz : z.forceSquare = 0 := le_antisymm (le_of_not_gt hh) hn
  rw [hz, zero_mul] at hc
  have hb := z.bending_pos_of_period hL
  nlinarith [sq_pos_of_pos hb]

theorem dilation_pos (hL : 0 < L) : 0 < a := by
  have hD := z.forceSquare_pos_of_period hL
  rw [z.forceSquare_eq] at hD
  have hprod : 0 < a*z.bending := by linarith
  exact (mul_pos_iff_of_pos_right (z.bending_pos_of_period hL)).mp hprod

theorem no_nonexpanding_periodic_profile (hL : 0 < L) (ha : a ≤ 0) : False :=
  not_lt_of_ge ha (z.dilation_pos hL)

theorem one_sign_centered_circle_of_period (hL : 0 < L)
    (hsign : (∀ s, 0 ≤ z.k s) ∨ (∀ s, z.k s ≤ 0)) :
    ∃ c : ℝ, c ≠ 0 ∧ c^4 = 2*a ∧ (∀ s, z.k s = c) ∧
      (∀ s, z.v s = 0) ∧ (∀ s, z.p s = -1/c) ∧ (∀ s, z.q s = 0) :=
  z.one_sign_centered_circle (z.dilation_pos hL) hL hsign

theorem both_curvature_excursions_of_period (hL : 0 < L)
    (hnonconstant : ¬∃ c : ℝ, ∀ s, z.k s = c) :
    (∃ s, z.k s < -z.curvatureRMS/2) ∧ (∃ s, z.curvatureRMS/2 < z.k s) :=
  z.both_curvature_excursions (z.dilation_pos hL) hL hnonconstant

end PeriodicSupportProfile
end
end ClosedSimilarity

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`ClosedSimilarity).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Soliton dilation audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Soliton-dilation audit passed: {checked} declarations; standard axioms only."
