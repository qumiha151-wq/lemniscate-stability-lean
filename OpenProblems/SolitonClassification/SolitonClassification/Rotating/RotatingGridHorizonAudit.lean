import SolitonClassification.Rotating.RotatingGridHorizonCandidate
import SolitonClassification.Rotating.RotatingGridMarginOrders
import SolitonClassification.Rotating.RotatingClosedProfileAudit

#print axioms SolitonClassification.Rotating.taylorPolynomial_margin_of_coarse
#print axioms SolitonClassification.Rotating.taylorPolynomial42_margin_uniform
#print axioms SolitonClassification.Rotating.extendedGridTime_signed_local_cap
#print axioms SolitonClassification.Rotating.extended_grid_actual_tube
#print axioms SolitonClassification.Rotating.candidate_parameter_time_domain
#print axioms SolitonClassification.Rotating.candidate_center_endpoint_preserved

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name || (`ClosedSimilarity).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating combined real time-neighborhood audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating combined real time-neighborhood audit passed for {count} declarations."
