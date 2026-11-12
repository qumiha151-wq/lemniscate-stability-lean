import SolitonClassification.Rotating.Block8Actual
#check SolitonClassification.Rotating.Block8.actual_original_derivative
#check SolitonClassification.Rotating.Block8.center_actual_state
#check SolitonClassification.Rotating.Block8.center_actual_matrix

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for ax in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Eight-leaf concrete assembly audit failed: {name} depends on {ax}"
      count := count+1
  logInfo m!"Eight-leaf concrete assembly audited: {count} declarations; standard axioms only."
