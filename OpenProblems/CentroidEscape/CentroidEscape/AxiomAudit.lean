import CentroidEscape
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  unless checked > 0 do throwError "No centroid declarations checked"
  logInfo m!"Centroid-escape audit passed: {checked} declarations; standard axioms only."
