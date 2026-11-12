import SolitonClassification.Rotating.Block8Leaf00
import SolitonClassification.Rotating.ExtendedPolynomialGridEndpoints42
import SolitonClassification.Rotating.RotatingGridHorizonCandidate
import SolitonClassification.Rotating.FlowMetricDeviationBootstrap
import SolitonClassification.Rotating.FlowMetricDeviationBudget

/-! Resource-control import: the same shared node header and analytic
dependencies as the eight-leaf assembly, but only the first concrete leaf.
This does not assert a grid or any additional numerical result. -/
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for ax in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Pilot baseline audit failed: {name} depends on {ax}"
      count := count+1
  logInfo m!"Pilot baseline audited: {count} declarations; standard axioms only."
