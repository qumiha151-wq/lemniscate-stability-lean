import SolitonClassification.Rotating.FirstFlowNeighborhood60
import SolitonClassification.Rotating.MatrixColumnNorm
import SolitonClassification.Rotating.MixedOrderVariation

/-! Aggregate audit for the finite-data-to-actual-first-segment milestone.
This file asserts no many-segment orbit or shooting root. -/
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Actual first-segment dependency audit passed for {count} declarations; standard axioms only."
