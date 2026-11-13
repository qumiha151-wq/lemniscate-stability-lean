module

public import SolitonClassification.Rotating.Endpoint4000Meaning
public import SolitonClassification.Rotating.CandidateInputs
public import SolitonClassification.Rotating.CandidatePreconditioner
public import SolitonClassification.Rotating.CandidateShootingEndpointComparison

@[expose] public section

/-! The finite comparisons are transported to the actual shooting map ONLY
under explicit two-sided actual tube and four actual endpoint-error premises.
Those premises must come from the complete signed grids, not the plan JSON. -/
namespace SolitonClassification.Rotating.Endpoint4000ActualComparison
open Set Metric Endpoint4000Data
noncomputable section
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option Elab.async false

def stateError : ℝ := 2400/10^32+1/10^55
def matrixError : ℝ := 2400/10^10+1/10^55

theorem phase_eq : Endpoint4000Finite.phase=Candidate.phase := rfl

theorem preconditioner_eq : Endpoint4000Finite.matrixOperator Endpoint4000Finite.rawB=
    CandidatePreconditioner.B := rfl

theorem comparison_matrix_eq : Endpoint4000Finite.matrixOperator Endpoint4000Finite.rawJ=
    CandidatePreconditioner.J := rfl

theorem endpoint_value_eq : Endpoint4000Finite.endpointValue=
    shootingEndpointValue plusState minusState := by
  ext i
  fin_cases i <;> simp [Endpoint4000Finite.endpointValue,shootingEndpointValue,
    shootingProjection_apply,shootingTarget]

theorem endpoint_derivative_eq :
    Endpoint4000Finite.matrixOperator Endpoint4000Finite.endpointJacobian=
      shootingEndpointDerivative CandidateInputs.phaseReal plusState minusState
        plusOperator minusOperator := by
  apply ContinuousLinearMap.ext
  intro u
  rw [Endpoint4000Meaning.derivative_formula,shootingEndpointDerivative_apply,
    shootingProjection_apply,shootingInitial_apply]
  simp only [Endpoint4000Meaning.endpointAction,Endpoint4000Meaning.projectReal,
    Endpoint4000Meaning.initialAction,CandidateInputs.phaseReal,phase_eq]

theorem proposed_endpoints_outer : plusState∈outerTube ∧ minusState∈outerTube := by
  norm_num [outerTube,plusState,minusState,plusCenters,minusCenters,mesh,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four]

theorem actual_center_enclosures {T R : ℝ} (hR : 0<R)
    (hplus : FlowTubeNeighborhood 1 (by norm_num) T Candidate.initial R)
    (hminus : FlowTubeNeighborhood (-1) (by norm_num) T Candidate.initial R)
    (ht : candidateParameterCenter 2∈Ioo 0 T)
    (hp : ‖plusState-supportFlow 1 (by norm_num)
      (candidateParameterCenter 2) Candidate.initial‖≤stateError)
    (hm : ‖minusState-supportFlow (-1) (by norm_num)
      (candidateParameterCenter 2) Candidate.initial‖≤stateError)
    (hPp : ‖plusOperator-fderiv ℝ (supportFlow 1 (by norm_num)
      (candidateParameterCenter 2)) Candidate.initial‖≤matrixError)
    (hPm : ‖minusOperator-fderiv ℝ (supportFlow (-1) (by norm_num)
      (candidateParameterCenter 2)) Candidate.initial‖≤matrixError) :
    ‖Endpoint4000Finite.value-
      actualShootingMap CandidateInputs.phaseReal candidateParameterCenter‖≤(1:ℝ)/10^27 ∧
    ‖CandidatePreconditioner.J-
      actualShootingDerivative CandidateInputs.phaseReal candidateParameterCenter‖≤(1:ℝ)/10^5 ∧
    ‖CandidatePreconditioner.B Endpoint4000Finite.value‖≤(1:ℝ)/10^30 := by
  have ha : shootingInitial CandidateInputs.phaseReal candidateParameterCenter∈
      ball Candidate.initial (R/4) := by
    rw [CandidateInputs.initial_state_eq,mem_ball,dist_self]
    positivity
  have hv:=actualShootingValue_endpoint_error CandidateInputs.phaseReal
    candidateParameterCenter plusState minusState
    (by simpa only [CandidateInputs.initial_state_eq] using hp)
    (by simpa only [CandidateInputs.initial_state_eq] using hm)
  have hd:=actualShootingDerivative_endpoint_error CandidateInputs.phaseReal
    CandidateInputs.phase_bounds.1 CandidateInputs.phase_bounds.2 T hR hplus hminus ht ha
    plusState minusState proposed_endpoints_outer.1 proposed_endpoints_outer.2
    plusOperator minusOperator
    (by simpa only [CandidateInputs.initial_state_eq] using hp)
    (by simpa only [CandidateInputs.initial_state_eq] using hm)
    (by simpa only [CandidateInputs.initial_state_eq] using hPp)
    (by simpa only [CandidateInputs.initial_state_eq] using hPm)
  have hvf:=Endpoint4000Finite.value_error
  rw [endpoint_value_eq] at hvf
  have hdf:=Endpoint4000Finite.jacobian_error
  rw [comparison_matrix_eq,endpoint_derivative_eq] at hdf
  refine ⟨?_,?_,?_⟩
  · exact ((norm_sub_le_norm_sub_add_norm_sub _
      (shootingEndpointValue plusState minusState) _).trans (add_le_add hvf hv)).trans
      (by norm_num [stateError])
  · exact ((norm_sub_le_norm_sub_add_norm_sub _
      (shootingEndpointDerivative CandidateInputs.phaseReal plusState minusState
        plusOperator minusOperator) _).trans (add_le_add hdf hd)).trans
      (by norm_num [stateError,matrixError])
  · simpa only [preconditioner_eq] using Endpoint4000Finite.preconditioned_value

end
end SolitonClassification.Rotating.Endpoint4000ActualComparison

#print axioms SolitonClassification.Rotating.Endpoint4000ActualComparison.actual_center_enclosures
open Lean Elab Command in
run_cmd do
  let name := `SolitonClassification.Rotating.Endpoint4000ActualComparison.actual_center_enclosures
  for ax in (←collectAxioms name) do
    unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
      throwError "Endpoint actual comparison audit failed: {name} depends on {ax}"
  logInfo "Endpoint conditional actual shooting comparison: standard three axioms only."
