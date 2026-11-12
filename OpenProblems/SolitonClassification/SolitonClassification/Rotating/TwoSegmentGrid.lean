import SolitonClassification.Rotating.GridResetEndpointData
import SolitonClassification.Rotating.PolynomialGridAssembly
import SolitonClassification.Rotating.FirstTrueState60

/-! Concrete two-segment positive-time reference grid. All node values,
full matrix inverse bounds and both terminal reset errors are discharged
by checked finite data. No whole 4000-step trajectory is asserted. -/
namespace SolitonClassification.Rotating.GridReset
noncomputable section
open Set Candidate UniversalMajorant
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

def nodeState (j : ℕ) : State := if j=0 then initial else if j=1 then state1 else state2
def nodeMatrix (j : ℕ) : FlowEnd := if j=0 then 1 else if j=1 then matrix1 else matrix2

theorem nodeState_inner (j : ℕ) (hj : j<2) : nodeState j∈innerTube := by
  interval_cases j
  · simpa [nodeState] using FirstResidualInteger60.initial_mem_innerTube
  · simpa [nodeState] using state1_mem_innerTube

theorem nodeMatrix_unit (j : ℕ) (hj : j≤2) : IsUnit (nodeMatrix j) := by
  interval_cases j
  · simp [nodeMatrix]
  · simpa [nodeMatrix] using matrix1_inverse.1
  · simpa [nodeMatrix] using matrix2_inverse.1

theorem nodeMatrix_bound (j : ℕ) (hj : j≤2) : ‖nodeMatrix j‖≤2 := by
  interval_cases j
  · norm_num [nodeMatrix]
  · simpa [nodeMatrix] using matrix1_norm
  · simpa [nodeMatrix] using matrix2_norm

theorem nodeMatrix_inverse_bound (j : ℕ) (hj : j≤2) : ‖Ring.inverse (nodeMatrix j)‖≤2 := by
  interval_cases j
  · norm_num [nodeMatrix]
  · simpa [nodeMatrix] using matrix1_inverse.2
  · simpa [nodeMatrix] using matrix2_inverse.2

theorem nodeState_reset (j : ℕ) (hj : j<2) :
    ‖polynomialPath (taylorPolynomial (nodeState j) 60) (1*(step:ℝ))-nodeState (j+1)‖≤1/10^57 := by
  interval_cases j
  · simpa [nodeState] using first_state_reset
  · simpa [nodeState] using second_state_reset

theorem nodeMatrix_reset (j : ℕ) (hj : j<2) :
    ‖referencePolynomialMatrix 1 (nodeState j) 22 (nodeMatrix j) (step:ℝ)-nodeMatrix (j+1)‖≤1/10^57 := by
  interval_cases j
  · simpa [nodeState,nodeMatrix,referencePolynomialMatrix,flowEnd_comp_one] using first_matrix_reset
  · simpa [nodeState,nodeMatrix,referencePolynomialMatrix] using second_matrix_reset

def twoSegmentGrid : FlowBootstrapGridData 1 2 (2*(step:ℝ)) 3 3 (1/10^54) (4/10^19) (1/10^57) :=
  polynomialGrid60_22 1 (by norm_num) 2 (step:ℝ) (1/10^54) (1/10^57) (1/10^57) nodeState nodeMatrix
    (Rat.cast_nonneg.mpr positive_step.le) (by exact Rat.cast_le.mpr step_below_cap.le)
    (by norm_num) nodeState_inner (by simp [nodeMatrix]) nodeMatrix_unit nodeMatrix_bound
    nodeMatrix_inverse_bound (by positivity) (by positivity) nodeState_reset nodeMatrix_reset

theorem two_time (j : ℕ) : twoSegmentGrid.time j=(j:ℝ)*(step:ℝ) := rfl

theorem two_initial_reference : twoSegmentGrid.reference 0 0=initial := by
  simp only [twoSegmentGrid,polynomialGrid60_22,Nat.cast_zero,zero_mul,shiftedPolynomialState_zero]
  simp [nodeState]

theorem two_terminal_reference : twoSegmentGrid.reference 2 (2*(step:ℝ))=state2 := by
  change shiftedPolynomialState 1 (nodeState 2) 60 (2*(step:ℝ)) (2*(step:ℝ))=state2
  rw [shiftedPolynomialState_zero]
  rfl

theorem two_terminal_matrix : twoSegmentGrid.matrix 2 (2*(step:ℝ))=matrix2 := by
  change shiftedPolynomialMatrix 1 (nodeState 2) 22 (nodeMatrix 2) (2*(step:ℝ)) (2*(step:ℝ))=matrix2
  rw [shiftedPolynomialMatrix_zero]
  rfl

theorem two_state_jump_sum : (∑j∈Finset.range 2,twoSegmentGrid.stateJump j)≤2/10^57 := by
  change (∑j∈Finset.range 2,(1:ℝ)/10^57)≤2/10^57
  norm_num

theorem two_matrix_jump_sum : (∑j∈Finset.range 2,twoSegmentGrid.matrixJump j)≤2/10^57 := by
  change (∑j∈Finset.range 2,(1:ℝ)/10^57)≤2/10^57
  norm_num

end
end SolitonClassification.Rotating.GridReset

#print axioms SolitonClassification.Rotating.GridReset.twoSegmentGrid
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Concrete two-segment 60/22 reference grid and all reset inputs checked."
