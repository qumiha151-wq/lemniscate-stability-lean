import LengthGrowth
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`FreeElasticScalar).isPrefixOf name || (`LengthGrowth).isPrefixOf name then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  unless checked > 0 do
    throwError "Axiom audit failed: no project declarations were checked"
  logInfo m!"Length-growth audit passed: {checked} declarations; standard axioms only."
