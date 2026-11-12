import SolitonClassification.ScalarReconstructionResidual
import SolitonClassification.OneSignCurvature

/-! The actual periodic support ODE implies the scalar equation. No curvature
division or additional regularity premise is used in this direction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace ClosedSimilarity.ScalarReconstruction

def profileSupportH {a b L : ℝ} (z : PeriodicSupportProfile a b L) (s : ℝ) : ℝ :=
  a*z.q s-b*z.p s

theorem force_eq_profileForce {a b L : ℝ} (z : PeriodicSupportProfile a b L) :
    force z.k=z.force := by
  have hk : deriv z.k=z.v := funext fun s => (z.dk s).deriv
  funext s
  dsimp only [force,PeriodicSupportProfile.force]
  rw [hk,(z.dv s).deriv]
  ring

theorem profileSupportH_hasDerivAt {a b L : ℝ}
    (z : PeriodicSupportProfile a b L) (s : ℝ) :
    HasDerivAt (profileSupportH z) (supportDerivative z.k a s) s := by
  convert ((z.dq s).const_mul a).sub ((z.dp s).const_mul b) using 1 <;>
    first | rfl | (simp only [supportDerivative,force_eq_profileForce z,
      PeriodicSupportProfile.force]; ring)

theorem force_hasDerivAt_of_profile {a b L : ℝ}
    (z : PeriodicSupportProfile a b L) (s : ℝ) :
    HasDerivAt (force z.k) (z.k s*profileSupportH z s-b) s := by
  rw [force_eq_profileForce z]
  convert ((z.dp s).const_mul (-a)).sub ((z.dq s).const_mul b) using 1 <;>
    first | rfl | (simp only [profileSupportH]; ring)

theorem numerator_eq_of_profile {a b L : ℝ}
    (z : PeriodicSupportProfile a b L) (s : ℝ) :
    numerator z.k b s=z.k s*profileSupportH z s := by
  dsimp only [numerator]
  rw [(force_hasDerivAt_of_profile z s).deriv]
  ring

theorem second_force_deriv_of_profile {a b L : ℝ}
    (z : PeriodicSupportProfile a b L) (s : ℝ) :
    deriv (deriv (force z.k)) s=
      z.v s*profileSupportH z s+z.k s*supportDerivative z.k a s := by
  have hf : deriv (force z.k)=fun u => z.k u*profileSupportH z u-b :=
    funext fun u => (force_hasDerivAt_of_profile z u).deriv
  rw [hf]
  exact (((z.dk s).mul (profileSupportH_hasDerivAt z s)).sub_const b).deriv

/-- Necessity holds for every actual support profile, including at all zeros
of curvature, and even when the soliton parameters both vanish. -/
theorem scalarEquation_of_periodicSupportProfile {a b L : ℝ}
    (z : PeriodicSupportProfile a b L) : ScalarEquation z.k a b := by
  intro s
  rw [second_force_deriv_of_profile z s,numerator_eq_of_profile z s,(z.dk s).deriv]
  ring

theorem profileSupportH_periodic {a b L : ℝ} (z : PeriodicSupportProfile a b L) :
    Function.Periodic (profileSupportH z) L := by
  intro s
  dsimp only [profileSupportH]
  rw [z.periodic_q s,z.periodic_p s]

end ClosedSimilarity.ScalarReconstruction

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`ClosedSimilarity).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Scalar necessity audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Scalar necessity audit passed for {count} declarations."
