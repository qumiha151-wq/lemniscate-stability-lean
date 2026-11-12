import SolitonClassification.Rotating.FlowBootstrapAudit
import SolitonClassification.Rotating.FlowMetricDeviationBootstrap
import SolitonClassification.Rotating.FlowMetricDeviationBudget

#print axioms SolitonClassification.Rotating.matrix_left_deviation_growth
#print axioms SolitonClassification.Rotating.metric_forward_deviation_reset_bound
#print axioms SolitonClassification.Rotating.FlowMetricGridData.actual_deviation_on_segment
#print axioms SolitonClassification.Rotating.FlowMetricGridData.metric_deviation_at_node
#print axioms SolitonClassification.Rotating.FlowBootstrapGridData.actualDeviation
#print axioms SolitonClassification.Rotating.FlowBootstrapGridData.actualDeviation_terminal
#print axioms SolitonClassification.Rotating.exp_deviation_budget

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating combined actual matrix-deviation audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating combined actual matrix-deviation audit passed for {count} declarations."
