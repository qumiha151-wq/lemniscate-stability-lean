module

public import SolitonClassification.Rotating.FullPathBlockEndpoints
public import SolitonClassification.Rotating.Endpoint4000ActualComparison

@[expose] public section

/-! Two genuine signed 4000-step blocks imply the actual final certificate
inputs, provided their exact initial and final states/matrices are identified.
This module does not construct either block and does not assert a root. -/
namespace SolitonClassification.Rotating.FullPathFinalInputs
noncomputable section
open Set Metric CandidateRootBudget Endpoint4000Data
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

abbrev PlusBlock := PolynomialPointGridBlock 1 (Candidate.step:ℝ) (1/10^55) (1/10^55) 4000
abbrev MinusBlock := PolynomialPointGridBlock (-1) (Candidate.step:ℝ) (1/10^55) (1/10^55) 4000

/-- Exactly the two uniform actual P/Q bounds and three actual shooting
enclosures required by the existing final root budget. -/
structure FinalInputs : Prop where
  plus : ActualFlowMatrixBounds 1 (by norm_num) horizon Candidate.initial tubeRadius initialSet 8000 16000
  minus : ActualFlowMatrixBounds (-1) (by norm_num) horizon Candidate.initial tubeRadius initialSet 8000 16000
  value : ‖Endpoint4000Finite.value-
    actualShootingMap CandidateInputs.phaseReal candidateParameterCenter‖≤(1:ℝ)/10^27
  jacobian : ‖CandidatePreconditioner.J-
    actualShootingDerivative CandidateInputs.phaseReal candidateParameterCenter‖≤(1:ℝ)/10^5
  residual : ‖CandidatePreconditioner.B Endpoint4000Finite.value‖≤(1:ℝ)/10^30

theorem state_error_eq : CandidateCenterEndpointBudget.endpointStateError=
    Endpoint4000ActualComparison.stateError := by
  norm_num [CandidateCenterEndpointBudget.endpointStateError,
    CandidateBootstrapBudget.centerMetricRadius,Endpoint4000ActualComparison.stateError]

theorem matrix_error_eq : CandidateCenterEndpointBudget.endpointMatrixError=
    Endpoint4000ActualComparison.matrixError := by
  norm_num [CandidateCenterEndpointBudget.endpointMatrixError,
    CandidateBootstrapBudget.centerRelativeError,Endpoint4000ActualComparison.matrixError]

theorem candidate_time_domain : candidateParameterCenter 2∈Ioo 0 horizon := by
  exact (parameter_domain (mem_closedBall_self radius_pos.le)).1

theorem tube_radius_pos : 0<tubeRadius := by
  have h:=radius_pos
  dsimp [tubeRadius]
  positivity

/-- No tube, flow existence, derivative error, inverse, or numerical residual
is newly assumed. All are derived from the genuine blocks and exact identities.
The endpoint identities concern the nominal time T0=4000*h, while the actual
uniform neighborhood covers the proved extended horizon T0+2*r. -/
theorem final_inputs_of_two_blocks
    (P : PlusBlock) (M : MinusBlock)
    (hP0 : P.state 0=Candidate.initial) (hPM0 : P.matrix 0=1)
    (hM0 : M.state 0=Candidate.initial) (hMM0 : M.matrix 0=1)
    (hPstate : P.state 4000=plusState) (hPmatrix : P.matrix 4000=plusOperator)
    (hMstate : M.state 4000=minusState) (hMmatrix : M.matrix 4000=minusOperator) :
    FinalInputs := by
  have hp:=FullPathBlock.actual_matrix_bounds (by norm_num : |(1:ℝ)|≤1) P hP0 hPM0
  have hm:=FullPathBlock.actual_matrix_bounds (by norm_num : |(-1:ℝ)|≤1) M hM0 hMM0
  have hpc:=FullPathBlock.actual_center_endpoints (by norm_num : |(1:ℝ)|≤1) P hP0 hPM0
  have hmc:=FullPathBlock.actual_center_endpoints (by norm_num : |(-1:ℝ)|≤1) M hM0 hMM0
  rw [hPstate,hPmatrix,state_error_eq,matrix_error_eq] at hpc
  rw [hMstate,hMmatrix,state_error_eq,matrix_error_eq] at hmc
  have he:=Endpoint4000ActualComparison.actual_center_enclosures tube_radius_pos
    hp.tube hm.tube candidate_time_domain
    (by simpa only [candidateParameterCenter,norm_sub_rev] using hpc.1)
    (by simpa only [candidateParameterCenter,norm_sub_rev] using hmc.1)
    (by simpa only [candidateParameterCenter,norm_sub_rev] using hpc.2)
    (by simpa only [candidateParameterCenter,norm_sub_rev] using hmc.2)
  exact ⟨hp,hm,he.1,he.2.1,he.2.2⟩

end
end SolitonClassification.Rotating.FullPathFinalInputs

#print axioms SolitonClassification.Rotating.FullPathFinalInputs.final_inputs_of_two_blocks
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf (privateToUserName name) then
      for ax in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Full-path final-input audit failed: {name} depends on {ax}"
      count := count+1
  logInfo m!"Full-path conditional final inputs: {count} declarations, standard three axioms only."
