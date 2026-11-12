import CentroidEscape.Shard_b_plus_s0500_n0050_bounded_Merge003_0000

#print axioms CentroidEscape.CertificateShards.Shard_b_plus_s0500_n0050_bounded.Merge003_0000.checked

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape.CertificateShards.Shard_b_plus_s0500_n0050_bounded).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Shard audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Strict shard audit passed for {count} declarations."
