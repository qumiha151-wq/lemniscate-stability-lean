import SolitonClassification.Rotating.FlowMetricAudit
import SolitonClassification.Rotating.FlowBootstrapMatrices

#print axioms SolitonClassification.Rotating.field_quadratic_remainder_bound
#print axioms SolitonClassification.Rotating.bootstrap_reference_segment
#print axioms SolitonClassification.Rotating.bootstrap_reset_bound
#print axioms SolitonClassification.Rotating.FlowBootstrapGridData.node_bound
#print axioms SolitonClassification.Rotating.FlowBootstrapGridData.actual_mem_outerTube
#print axioms SolitonClassification.Rotating.FlowBootstrapGridData.tubeNeighborhood
#print axioms SolitonClassification.Rotating.FlowBootstrapGridData.actualMatrixBounds_8000_16000

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating combined actual state-bootstrap audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating combined actual state-bootstrap audit passed for {count} declarations."
