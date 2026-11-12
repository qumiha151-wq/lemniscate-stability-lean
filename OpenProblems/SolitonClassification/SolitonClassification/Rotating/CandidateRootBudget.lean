import SolitonClassification.Rotating.CandidateInputs
import SolitonClassification.Rotating.CandidatePreconditioner
import SolitonClassification.Rotating.FlowInverseRoot

/-! Concrete scalar and domain choices for the final candidate certificate.
The two actual full-horizon matrix bounds and three numerical enclosures
remain explicit inputs. No particular shooting root is yet certified. -/
namespace SolitonClassification.Rotating.CandidateRootBudget
noncomputable section
open Set Metric
open scoped NNReal
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

def radius : ℝ := (candidateWideTimeRadius:ℝ)
def initialSet : Set State := closedBall Candidate.initial radius
def tubeRadius : ℝ := 8*radius
def horizon : ℝ := candidateWideExtendedHorizon
def contraction : ℝ≥0 := 1/50

theorem radius_pos : 0<radius := candidate_wide_time_radius_pos

theorem horizon_bounds : 0<horizon ∧ horizon<32 := by
  have h:=candidate_extension_for_radius (r:=radius) le_rfl
  have hr:=radius_pos
  change 0<(Candidate.parameters 2:ℝ)+2*radius ∧ (Candidate.parameters 2:ℝ)+2*radius<32
  exact ⟨by linarith [h.2.1],h.2.2⟩

theorem variation_budget : 16*trueJointVariationBudget horizon 8000 16000≤10^20 := by
  calc
    _ ≤ 16*trueJointVariationBudget 32 8000 16000 := by
      dsimp [trueJointVariationBudget]
      nlinarith [horizon_bounds.2]
    _ ≤ 10^20 := by norm_num [trueJointVariationBudget]

theorem contraction_budget : (1:ℝ)/10^10+
    82*(1/10^5+(16*trueJointVariationBudget horizon 8000 16000)*radius)≤(contraction:ℝ) := by
  calc
    _ ≤ (1:ℝ)/10^10+82*(1/10^5+10^20*radius) := by
      nlinarith [mul_le_mul_of_nonneg_right variation_budget radius_pos.le]
    _ ≤ (contraction:ℝ) := by norm_num [contraction,radius,candidateWideTimeRadius]

theorem self_map_budget : ((1:ℝ)/10^30+82*(1/10^27))+(contraction:ℝ)*radius≤radius := by
  norm_num [contraction,radius,candidateWideTimeRadius]

theorem parameter_domain {c : Parameters} (hc : c∈closedBall candidateParameterCenter radius) :
    c 2∈Ioo 0 horizon ∧ shootingInitial CandidateInputs.phaseReal c∈initialSet :=
  ⟨candidate_wide_parameter_time_domain hc,CandidateInputs.initial_mem_closedBall hc⟩

theorem initial_set_inside_quarter_tube : initialSet⊆ball Candidate.initial (tubeRadius/4) :=
  CandidateInputs.initial_set_subset_quarter_tube radius_pos

/-- All domain, preconditioner and scalar contraction arithmetic is discharged.
The remaining premises concern the actual full positive/negative flows and
actual shooting value/derivative; fixed rational data do not replace them. -/
theorem exists_unique_zero_of_remaining_enclosures
    (plus : ActualFlowMatrixBounds 1 (by norm_num) horizon Candidate.initial tubeRadius initialSet 8000 16000)
    (minus : ActualFlowMatrixBounds (-1) (by norm_num) horizon Candidate.initial tubeRadius initialSet 8000 16000)
    (y : Parameters)
    (hvalue : ‖y-actualShootingMap CandidateInputs.phaseReal candidateParameterCenter‖≤(1:ℝ)/10^27)
    (hjacobian : ‖CandidatePreconditioner.J-
      actualShootingDerivative CandidateInputs.phaseReal candidateParameterCenter‖≤(1:ℝ)/10^5)
    (hresidual : ‖CandidatePreconditioner.B y‖≤(1:ℝ)/10^30) :
    ∃c∈closedBall candidateParameterCenter radius,
      actualShootingMap CandidateInputs.phaseReal c=0 ∧
        ∀c'∈closedBall candidateParameterCenter radius,
          actualShootingMap CandidateInputs.phaseReal c'=0 → c'=c := by
  exact exists_unique_actual_shooting_zero_of_actual_matrix_bounds
    CandidateInputs.phaseReal CandidateInputs.phase_bounds.1 CandidateInputs.phase_bounds.2
    horizon_bounds.1.le (by have hr:=radius_pos; dsimp [tubeRadius]; positivity)
    (by norm_num) (by norm_num) (convex_closedBall Candidate.initial radius)
    initial_set_inside_quarter_tube plus minus CandidatePreconditioner.B CandidatePreconditioner.J
    candidateParameterCenter y contraction radius_pos.le (by norm_num)
    (by norm_num [contraction]) (by norm_num)
    (fun _ hc=>parameter_domain hc) hvalue hjacobian
    CandidatePreconditioner.actual_preconditioner_norm CandidatePreconditioner.actual_preconditioner_defect
    hresidual contraction_budget self_map_budget

end
end SolitonClassification.Rotating.CandidateRootBudget

#print axioms SolitonClassification.Rotating.CandidateRootBudget.exists_unique_zero_of_remaining_enclosures
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Candidate root budget audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Fixed candidate scalar/domain budget audited: {count} declarations; standard axioms only."
