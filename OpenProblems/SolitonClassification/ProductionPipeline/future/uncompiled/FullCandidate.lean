module

public import SolitonClassification.Rotating.FullGridPActual
public import SolitonClassification.Rotating.FullGridMActual
public import SolitonClassification.Rotating.FullPathFinalGeometry

@[expose] public section

/-! Assembly source awaiting the full 250-shard kernel check. Its presence
does not certify the candidate. No placeholder axioms or assumed grid values
are supplied: both concrete grids and all eight identities must import. -/
namespace SolitonClassification.Rotating.FullCandidate
noncomputable section
set_option Elab.async false

/-- Intended final application to the two concrete signed grids. The exact
geometric conclusion includes nonconstant curvature, nonzero normal rotation,
and the actual pure-normal elastic flow. Its closing period is not asserted
to be minimal. -/
theorem exists_closed_rotating_elastic_flow :
    ∃c : Parameters, ∃X Y : ℝ → ℝ → ℝ,
      CandidateFinalAssembly.GeometricConclusion c X Y := by
  exact FullPathFinalGeometry.exists_geometry_of_two_blocks
    FullGridP.certificate FullGridM.certificate
    FullGridP.state_start FullGridP.matrix_start
    FullGridM.state_start FullGridM.matrix_start
    FullGridPActual.terminal_state FullGridPActual.terminal_matrix
    FullGridMActual.terminal_state FullGridMActual.terminal_matrix

end
end SolitonClassification.Rotating.FullCandidate

#print axioms SolitonClassification.Rotating.FullCandidate.exists_closed_rotating_elastic_flow
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    let userName := privateToUserName name
    if (`SolitonClassification.Rotating).isPrefixOf userName ||
        (`ClosedSimilarity).isPrefixOf userName then
      for ax in (← collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Full candidate audit failed: {name} depends on {ax}"
      count := count + 1
  logInfo m!"Full candidate actual geometry: {count} declarations; standard three axioms only."
