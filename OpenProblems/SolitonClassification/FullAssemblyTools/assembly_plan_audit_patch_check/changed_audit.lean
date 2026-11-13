module
public import SolitonClassification.Rotating.FullPathFinalGeometry
#check SolitonClassification.Rotating.FullPathFinalGeometry.exists_geometry_of_two_blocks
#print axioms SolitonClassification.Rotating.FullPathFinalGeometry.exists_geometry_of_two_blocks
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (←getEnv).constants do
    let userName := privateToUserName name
    if (`SolitonClassification.Rotating).isPrefixOf userName || (`ClosedSimilarity).isPrefixOf userName then
      for ax in (←collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Unexpected axiom: {name} depends on {ax}"
      count := count + 1
  unless count == 2205 do throwError "Unexpected imported declaration count: {count}"
  logInfo "FINAL_SUPPLEMENT_CONDITIONAL_AUDIT 2205"

-- changed source
