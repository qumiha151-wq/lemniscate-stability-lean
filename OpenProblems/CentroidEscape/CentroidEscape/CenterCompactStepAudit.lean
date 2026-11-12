import CentroidEscape.CenterFirstEleven

open Lean Elab Command in
run_cmd do
  let start ← IO.monoMsNow
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape.CenterCompactData).isPrefixOf name ||
        name == `CentroidEscape.checkedStagesExtend then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Compact-step audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Compact-step strict audit passed for {checked} declarations in {(← IO.monoMsNow)-start} ms."
