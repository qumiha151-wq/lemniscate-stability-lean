module
public import SolitonClassification.Rotating.FullGridM
public import SolitonClassification.Rotating.Endpoint4000Data
public import SolitonClassification.Rotating.FullPathBlockEndpoints

@[expose] public section
namespace SolitonClassification.Rotating.FullGridMActual
noncomputable section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem centers_equal : RM3968B03Nodes.centers 8=Endpoint4000Data.minusCenters := by
  funext i; fin_cases i <;> decide +kernel
theorem matrices_equal : RM3968B03Nodes.matrix 8=Endpoint4000Data.minusMatrix := by
  funext c i; fin_cases c <;> fin_cases i <;> decide +kernel
theorem terminal_state : FullGridM.certificate.state 4000=Endpoint4000Data.minusState := by
  rw [FullGridM.state_last]
  funext i
  change (((RM3968B03Nodes.centers 8 i:ℚ)/Candidate.mesh:ℚ):ℝ)=_
  rw [centers_equal]
  exact Endpoint4000Data.minusState_cast i
theorem terminal_matrix : FullGridM.certificate.matrix 4000=Endpoint4000Data.minusOperator := by
  rw [FullGridM.matrix_last]
  exact congrArg (pointMatrixOperator Candidate.mesh) matrices_equal

theorem actual_center_endpoints :
    ‖supportFlow (-1:ℝ) (by norm_num) (Candidate.parameters 2:ℝ) Candidate.initial-
        Endpoint4000Data.minusState‖≤CandidateCenterEndpointBudget.endpointStateError ∧
    ‖fderiv ℝ (supportFlow (-1:ℝ) (by norm_num) (Candidate.parameters 2:ℝ)) Candidate.initial-
        Endpoint4000Data.minusOperator‖≤CandidateCenterEndpointBudget.endpointMatrixError := by
  have h := FullPathBlock.actual_center_endpoints (by norm_num : |(-1:ℝ)|≤1)
    FullGridM.certificate FullGridM.state_start FullGridM.matrix_start
  rwa [terminal_state,terminal_matrix] at h

theorem actual_matrix_bounds :
    ActualFlowMatrixBounds (-1:ℝ) (by norm_num) CandidateRootBudget.horizon Candidate.initial
      CandidateRootBudget.tubeRadius CandidateRootBudget.initialSet 8000 16000 :=
  FullPathBlock.actual_matrix_bounds (by norm_num) FullGridM.certificate FullGridM.state_start FullGridM.matrix_start

end
end SolitonClassification.Rotating.FullGridMActual
end
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf (privateToUserName name) then
      for ax in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Grid assembly audit failed: {name} depends on {ax}"
      count := count + 1
  logInfo m!"ActualFullGrid_M: {count} declarations; standard axioms only."
