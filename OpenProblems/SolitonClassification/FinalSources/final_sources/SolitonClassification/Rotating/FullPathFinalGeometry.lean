module

public import SolitonClassification.Rotating.FullPathFinalInputs
public import SolitonClassification.Rotating.CandidateFinalAssembly

@[expose] public section

/-! The complete conditional implication from two genuine signed blocks to
closed nonconstant rotating geometry and its actual pure-normal FEF. Neither
block, nor its data identities, is constructed or assumed proved here. -/
namespace SolitonClassification.Rotating.FullPathFinalGeometry
noncomputable section
open FullPathFinalInputs Endpoint4000Data CandidateFinalAssembly
set_option Elab.async false

/-- Two certified signed 4000-step blocks and eight exact initial/endpoint
identities suffice. There is no new zero, tube, periodicity, regularity, or
geometric premise. The conclusion retains the precise candidate ball,
nonconstant curvature, nonzero normal rotation, total curvature -56*(2*pi),
closing period 114*c2, and future-global actual pure-normal elastic PDE. -/
theorem exists_geometry_of_two_blocks
    (P : PlusBlock) (M : MinusBlock)
    (hP0 : P.state 0=Candidate.initial) (hPM0 : P.matrix 0=1)
    (hM0 : M.state 0=Candidate.initial) (hMM0 : M.matrix 0=1)
    (hPstate : P.state 4000=plusState) (hPmatrix : P.matrix 4000=plusOperator)
    (hMstate : M.state 4000=minusState) (hMmatrix : M.matrix 4000=minusOperator) :
    ∃c : Parameters,∃X Y : ℝ → ℝ → ℝ,GeometricConclusion c X Y := by
  have h:=final_inputs_of_two_blocks P M hP0 hPM0 hM0 hMM0
    hPstate hPmatrix hMstate hMmatrix
  exact exists_geometry_and_pure_normal_evolution_of_remaining_enclosures
    h.plus h.minus Endpoint4000Finite.value h.value h.jacobian h.residual

end
end SolitonClassification.Rotating.FullPathFinalGeometry

#print axioms SolitonClassification.Rotating.FullPathFinalGeometry.exists_geometry_of_two_blocks
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    let userName:=privateToUserName name
    if (`SolitonClassification.Rotating).isPrefixOf userName ||
        (`ClosedSimilarity).isPrefixOf userName then
      for ax in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Full-path geometry audit failed: {name} depends on {ax}"
      count:=count+1
  logInfo m!"Full-path conditional closed geometry: {count} declarations; standard three axioms only."
