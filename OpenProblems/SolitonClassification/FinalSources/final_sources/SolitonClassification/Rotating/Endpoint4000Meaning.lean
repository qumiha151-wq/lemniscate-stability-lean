module

public import SolitonClassification.Rotating.Endpoint4000Finite

@[expose] public section

/-! Polynomial meaning of the finite shooting matrix, with the actual field
evaluated at the proposed endpoints. These identities do not assert that
the proposed endpoints or matrices enclose an actual flow. -/
namespace SolitonClassification.Rotating.Endpoint4000Meaning
open Endpoint4000Data Endpoint4000Finite
noncomputable section
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option Elab.async false

def initialAction (u : ParameterVector) : State :=
  ![u 0,u 3*(phase 0:ℝ)/8,u 1,u 3*(phase 1:ℝ),u 4,0]

def projectReal (x : State) : ParameterVector := ![x 0,8*x 1,x 2,x 3,x 5]

def endpointAction (u : ParameterVector) : ParameterVector :=
  projectReal ((u 2) • (field plusState+field minusState)+
    (plusOperator-minusOperator) (initialAction u))

theorem field_cast (x : Fin 6 → ℚ) (i : Fin 6) :
    (rawField x i:ℝ)=field (fun j=>(x j:ℝ)) i := by
  fin_cases i <;> simp [rawField,field]

theorem matrix_apply (M : PointMatrix) (x : State) (i : Fin 6) :
    pointMatrixOperator mesh M x i=∑j : Fin 6,x j*((M j i:ℝ)/(mesh:ℝ)) := by
  simp [pointMatrixOperator,rationalColumnOperator,columnOperator_apply]

theorem derivative_formula (u : ParameterVector) :
    matrixOperator endpointJacobian u=endpointAction u := by
  ext i
  fin_cases i <;>
    simp [matrixOperator_apply,endpointJacobian,endpointColumns,projected,
      deltaColumn,endpointAction,projectReal,initialAction,plusOperator,minusOperator,
      matrix_apply,Fin.sum_univ_succ,rawField,
      field,←plusState_cast,←minusState_cast]
  all_goals ring

end
end SolitonClassification.Rotating.Endpoint4000Meaning

#print axioms SolitonClassification.Rotating.Endpoint4000Meaning.derivative_formula
open Lean Elab Command in
run_cmd do
  let name := `SolitonClassification.Rotating.Endpoint4000Meaning.derivative_formula
  for ax in (←collectAxioms name) do
    unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
      throwError "Endpoint meaning audit failed: {name} depends on {ax}"
  logInfo "Endpoint actual-field/full-matrix meaning: standard three axioms only."
