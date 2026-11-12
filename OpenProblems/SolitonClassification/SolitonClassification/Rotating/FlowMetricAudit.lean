import SolitonClassification.Rotating.FlowInverseAudit
import SolitonClassification.Rotating.FlowMetricRoot

#print axioms SolitonClassification.Rotating.flowMetricForward_hasDerivWithinAt
#print axioms SolitonClassification.Rotating.flowMetricInverse_hasDerivWithinAt
#print axioms SolitonClassification.Rotating.metric_inverse_reset_bound
#print axioms SolitonClassification.Rotating.FlowMetricGridData.actual_matrix_bounds
#print axioms SolitonClassification.Rotating.actualFlowMatrixBounds_8000_16000_of_reference_grids

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating combined actual moving-matrix audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating combined actual moving-matrix audit passed for {count} declarations."
