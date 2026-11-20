import SolitonClassification.Reflected.NumericInput
import SolitonClassification.Reflected.AllTrajectory
import SolitonClassification.Reflected.MinusTrajectory
import SolitonClassification.Reflected.PlusTrajectory

namespace SolitonClassification.Reflected
open SolitonClassification.Rotating Set

theorem first_reflected_shooting_zero :
    ∃b∈slopes, ∃t∈times, velocity (b,t)=0 ∧ tangentSupport (b,t)=0 ∧
      ∀x∈Icc 0 t, shot b x ∈ outerTube := by
  have ht : (740:ℝ)*(traceStep:ℝ)=center := by norm_num [traceStep,center]
  apply trajectory_event
  · rw [←ht]
    exact AllTrajectory.trajectory
  · rw [←ht]
    exact MinusTrajectory.trajectory
  · rw [←ht]
    exact PlusTrajectory.trajectory

end SolitonClassification.Reflected
#print axioms SolitonClassification.Reflected.first_reflected_shooting_zero

open Lean Elab Command in
run_cmd do
  let mut checked : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Reflected).isPrefixOf name then
      for ax in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Unapproved axiom in {name}: {ax}"
      checked := checked+1
  logInfo m!"Reflected shooting proof audited {checked} declarations."
