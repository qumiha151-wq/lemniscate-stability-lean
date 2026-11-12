import SolitonClassification.Rotating.GridResetStep1Matrix22
import SolitonClassification.Rotating.FixedEndpointReset
import SolitonClassification.Rotating.VariationLinearity

/-! Both finite segments have real polynomial endpoint bounds, including
the final reset. Exact matrix midpoint invertibility is checked by a full
row-sum bound and the Neumann theorem. No actual orbit error is assumed. -/
namespace SolitonClassification.Rotating.GridReset
noncomputable section
open Candidate
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rawState2 (i : Fin 6) : ℚ := (GridResetStep1State60.endpointData[i.val].center:ℚ)/mesh
def state2 : State := fun i=>(rawState2 i:ℝ)
def rawMatrix2 (j i : Fin 6) : ℚ := ((GridResetStep1Matrix22.fullEndpoint j)[i.val].center:ℚ)/mesh
def matrix2 : FlowEnd := rationalColumnOperator rawMatrix2

theorem matrix2_rows_checked : ∀i : Fin 6,∑j : Fin 6,|rawMatrix2 j i|≤2 := by decide +kernel
theorem matrix2_identity_rows_checked : ∀i : Fin 6,
    ∑j : Fin 6,|rawMatrix2 j i-(if i=j then 1 else 0)|≤1/2 := by decide +kernel

theorem matrix2_norm : ‖matrix2‖≤2 := by
  convert! rationalColumnOperator_norm_le rawMatrix2 (by norm_num) matrix2_rows_checked using 1

theorem matrix2_identity_error : ‖matrix2-1‖≤1/2 := by
  convert! rationalColumnOperator_sub_one_norm_le rawMatrix2 (by norm_num) matrix2_identity_rows_checked using 1
  norm_num

theorem matrix2_inverse : IsUnit matrix2 ∧ ‖Ring.inverse matrix2‖≤2 := by
  have h := flowEnd_inverse_bound_of_norm_sub_one_le matrix2 matrix2_identity_error (by norm_num)
  norm_num at h
  exact h

theorem first_state_radius_checked : ∀i : Fin 6,
    (BenchState60.endpointData[i.val].radius:ℚ)/mesh≤1/10^57 := by decide +kernel

theorem second_state_radius_checked : ∀i : Fin 6,
    (GridResetStep1State60.endpointData[i.val].radius:ℚ)/mesh≤1/10^57 := by decide +kernel

theorem first_matrix_radius_rows_checked : ∀i : Fin 6,
    ∑j : Fin 6,((BenchMatrix22.fullEndpoint j)[i.val].radius:ℚ)/mesh≤1/10^57 := by decide +kernel

theorem second_matrix_radius_rows_checked : ∀i : Fin 6,
    ∑j : Fin 6,((GridResetStep1Matrix22.fullEndpoint j)[i.val].radius:ℚ)/mesh≤1/10^57 := by decide +kernel

theorem first_state_reset : ‖polynomialPath (taylorPolynomial initial 60) (step:ℝ)-state1‖≤1/10^57 := by
  have h := fixedStateMidpoint_error BenchState60.endpoint_enclosed (by norm_num) first_state_radius_checked
  convert! h using 1
  norm_num

theorem second_state_reset : ‖polynomialPath (taylorPolynomial state1 60) (step:ℝ)-state2‖≤1/10^57 := by
  have h := fixedStateMidpoint_error GridResetStep1State60.endpoint_enclosed (by norm_num) second_state_radius_checked
  convert! h using 1
  norm_num

theorem first_matrix_reset : ‖variationPolynomialMap initial 22 (step:ℝ)-matrix1‖≤1/10^57 := by
  have he (j i : Fin 6) : ((BenchMatrix22.fullEndpoint j)[i.val]).Contains mesh
      (variationPolynomialMap initial 22 (step:ℝ) (coordinateBasis j) i) := by
    rw [variationPolynomialMap_apply]
    exact BenchMatrix22.full_matrix_enclosed j i
  have h := fixedMatrixMidpoint_error he (by norm_num) first_matrix_radius_rows_checked
  convert! h using 1
  norm_num

theorem second_matrix_reset :
    ‖(variationPolynomialMap state1 22 (step:ℝ)).comp matrix1-matrix2‖≤1/10^57 := by
  have he (j i : Fin 6) : ((GridResetStep1Matrix22.fullEndpoint j)[i.val]).Contains mesh
      ((variationPolynomialMap state1 22 (step:ℝ)).comp matrix1 (coordinateBasis j) i) := by
    simp only [ContinuousLinearMap.comp_apply,variationPolynomialMap_apply]
    exact GridResetStep1Matrix22.full_matrix_enclosed j i
  have h := fixedMatrixMidpoint_error he (by norm_num) second_matrix_radius_rows_checked
  convert! h using 1
  norm_num

end
end SolitonClassification.Rotating.GridReset

#print axioms SolitonClassification.Rotating.GridReset.second_matrix_reset
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Both state and full-matrix reset jumps, including terminal reset, kernel checked."
