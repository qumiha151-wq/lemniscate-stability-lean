import SolitonClassification.Rotating.ActualFlowAudit
import SolitonClassification.Rotating.FlowInverseRoot
import SolitonClassification.Rotating.FlowInverseODE

#print axioms SolitonClassification.Rotating.supportFlow_fderiv_isUnit
#print axioms SolitonClassification.Rotating.supportFlow_inverse_continuousOn
#print axioms SolitonClassification.Rotating.supportFlow_inverse_hasDerivWithinAt
#print axioms SolitonClassification.Rotating.exists_unique_actual_shooting_zero_of_actual_matrix_bounds

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating actual canonical-inverse combined audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating actual canonical-inverse combined audit passed for {count} declarations."
