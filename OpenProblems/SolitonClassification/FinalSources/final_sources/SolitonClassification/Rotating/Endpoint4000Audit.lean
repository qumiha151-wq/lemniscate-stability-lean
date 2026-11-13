module

public import SolitonClassification.Rotating.Endpoint4000ActualComparison

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf (privateToUserName name) then
      for ax in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Endpoint complete imported-chain audit failed: {name} depends on {ax}"
      count := count+1
  logInfo m!"Endpoint complete imported-chain audit passed: {count} declarations, standard three axioms only."
