module

public import SolitonClassification.Rotating.CandidateBootstrapBudget
public import SolitonClassification.Rotating.CandidateShootingEndpointComparison

@[expose] public section

/-! The existing center radius suffices for the actual unpreconditioned value
threshold. Last nominal resets are charged; finite value/J comparisons remain
explicit inputs. No new trajectory or root is asserted. -/
namespace SolitonClassification.Rotating.CandidateCenterEndpointBudget
noncomputable section
open CandidateBootstrapBudget
set_option Elab.async false

def endpointStateError : ℝ := 2400*centerMetricRadius+1/10^55
def endpointMatrixError : ℝ := 2400*centerRelativeError+1/10^55
def numericValueBudget : ℝ := 1/10^30
def numericDerivativeBudget : ℝ := 6/10^6

theorem full_internal_state_reset_budget :
    (3999:ℝ)*(1/10^55)≤stateResetBudget := by
  norm_num [stateResetBudget]

theorem full_internal_matrix_reset_budget :
    (3999:ℝ)*(1/10^55)≤matrixResetBudget := by
  norm_num [matrixResetBudget]

theorem full_nominal_time_exact :
    (4000:ℝ)*(Candidate.step:ℝ)=(Candidate.parameters 2:ℝ) := by
  simp only [Candidate.step,Rat.cast_div,Rat.cast_ofNat]
  ring

theorem value_budget : numericValueBudget+16*endpointStateError<(1:ℝ)/10^27 := by
  norm_num [numericValueBudget,endpointStateError,centerMetricRadius]

theorem derivative_budget : numericDerivativeBudget+
    16*(17*endpointStateError+endpointMatrixError)<(1:ℝ)/10^5 := by
  norm_num [numericDerivativeBudget,endpointStateError,endpointMatrixError,
    centerMetricRadius,centerRelativeError]

/-- This deliberately compares the unpreconditioned value error with hvalue's
1e-27 threshold. The factor 82 belongs later in the existing self-map bound. -/
theorem actual_value_enclosure (e : Fin 2 → ℝ) (p : Parameters)
    (xp xm : State) (y : Parameters)
    (hp : ‖xp-supportFlow 1 (by norm_num) (p 2) (shootingInitial e p)‖≤endpointStateError)
    (hm : ‖xm-supportFlow (-1) (by norm_num) (p 2) (shootingInitial e p)‖≤endpointStateError)
    (hy : ‖y-shootingEndpointValue xp xm‖≤numericValueBudget) :
    ‖y-actualShootingMap e p‖≤(1:ℝ)/10^27 := by
  have h:=actualShootingValue_endpoint_error e p xp xm hp hm
  exact ((norm_sub_le_norm_sub_add_norm_sub y (shootingEndpointValue xp xm)
    (actualShootingMap e p)).trans (add_le_add hy h)).trans value_budget.le

theorem actual_derivative_enclosure (e : Fin 2 → ℝ) (p : Parameters)
    (xp xm : State) (Pp Pm : State →L[ℝ] State)
    (J : Parameters →L[ℝ] Parameters)
    (hactual : ‖shootingEndpointDerivative e xp xm Pp Pm-actualShootingDerivative e p‖≤
      16*(17*endpointStateError+endpointMatrixError))
    (hfinite : ‖J-shootingEndpointDerivative e xp xm Pp Pm‖≤numericDerivativeBudget) :
    ‖J-actualShootingDerivative e p‖≤(1:ℝ)/10^5 := by
  exact ((norm_sub_le_norm_sub_add_norm_sub J (shootingEndpointDerivative e xp xm Pp Pm)
    (actualShootingDerivative e p)).trans (add_le_add hfinite hactual)).trans derivative_budget.le

end
end SolitonClassification.Rotating.CandidateCenterEndpointBudget

#print axioms SolitonClassification.Rotating.CandidateCenterEndpointBudget.actual_value_enclosure
#print axioms SolitonClassification.Rotating.CandidateCenterEndpointBudget.actual_derivative_enclosure
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf (privateToUserName name) then
      for ax in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Candidate center endpoint budget failed: {name} depends on {ax}"
      count := count+1
  logInfo m!"Candidate center endpoint budget audited: {count} declarations; standard axioms only."
