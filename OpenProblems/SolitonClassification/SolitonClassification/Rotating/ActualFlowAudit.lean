import SolitonClassification.Rotating.ActualRootFromMatrices
import SolitonClassification.Rotating.FlowTube

/-! Combined audit of the independent actual-flow/variation/root bridge.
This is not an instantiation of the numerical rotating candidate. -/
#print axioms SolitonClassification.Rotating.supportFlow_short_original
#print axioms SolitonClassification.Rotating.supportFlow_hasStrictFDerivAt_joint
#print axioms SolitonClassification.Rotating.supportFlow_fderiv_integral
#print axioms SolitonClassification.Rotating.field_second_fderiv_bound
#print axioms SolitonClassification.Rotating.supportFlow_fderiv_sharp_variation
#print axioms SolitonClassification.Rotating.actualShootingDerivative_sharp_variation
#print axioms SolitonClassification.Rotating.exists_unique_actual_shooting_zero_of_true_matrices

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating combined actual-flow audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating combined actual-flow audit passed for {count} declarations."
