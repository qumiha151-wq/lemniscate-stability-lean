import SolitonClassification.Rotating.FirstPolynomial60
import SolitonClassification.Rotating.MetricReset
import SolitonClassification.Rotating.ResidualODE
import SolitonClassification.Rotating.ShootingRoot

/-! Audit of the first independent formalization milestone.
This file does not assert existence of a rotating periodic orbit. -/
#print axioms SolitonClassification.Rotating.Candidate.first_polynomial60_computed
#print axioms SolitonClassification.Rotating.Candidate.first_polynomial60_enclosed
#print axioms SolitonClassification.Rotating.polynomial_ode_comparison

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      count := count+1
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
  logInfo m!"Rotating first-milestone audit passed for {count} namespace declarations; standard axioms only."
