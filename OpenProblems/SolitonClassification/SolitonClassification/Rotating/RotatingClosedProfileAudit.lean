import SolitonClassification.Rotating.FlowMetricDeviationAudit
import SolitonClassification.Rotating.RotatingClosedProfileNonconstant

#print axioms SolitonClassification.Rotating.rotatingTrajectory_quasiperiodic
#print axioms SolitonClassification.Rotating.rotatingTrajectory_global_tube
#print axioms SolitonClassification.Rotating.rotatingTrajectory_smooth
#print axioms SolitonClassification.Rotating.periodicRotatingSupport
#print axioms SolitonClassification.Rotating.closed_rotating_profile_of_endpoint
#print axioms SolitonClassification.Rotating.actualShooting_closed_profile
#print axioms SolitonClassification.Rotating.actualShooting_total_curvature
#print axioms SolitonClassification.Rotating.actualShooting_nonconstant_rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name || (`ClosedSimilarity).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating combined conditional closed-geometry audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating combined conditional closed-geometry audit passed for {count} declarations."
