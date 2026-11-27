import BernoulliBridge.BernoulliNonmigration
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let declarations := #[`Lemniscate.bernoulli_all_time_height_bound,
    `Lemniscate.bernoulli_all_time_graph_from_initial_curvature,
    `Lemniscate.bernoulli_oriented_graph_tracks,
    `Lemniscate.bernoulli_oriented_graph_disk_of_height,
    `Lemniscate.bernoulli_oriented_graph_disk,
    `Lemniscate.bernoulli_nonmigration_from_initial_curvature]
  for name in declarations do
    unless (← getEnv).contains name do
      throwError "Missing declaration {name}"
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on {axiomName}"
  logInfo m!"Bernoulli migration bridge verified {declarations.size} theorems with standard axioms only."
