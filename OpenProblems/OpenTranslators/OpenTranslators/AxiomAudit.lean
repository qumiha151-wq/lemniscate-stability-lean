import OpenTranslators
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`OpenTranslator).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  unless checked > 0 do throwError "No translator declarations checked"
  logInfo m!"Open-translator audit passed: {checked} declarations; standard axioms only."
