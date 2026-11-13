module

public import SolitonClassification.Rotating.PolynomialPointGridBlockGrid
public import SolitonClassification.Rotating.CandidateCenterEndpointBudget

@[expose] public section

/-! Actual full-horizon consequences of a genuine 4000-step point block.
This theorem does not provide that block: all numerical shard and seam proofs
must first construct it. Center accuracy and the parameter ball are separate. -/
namespace SolitonClassification.Rotating.FullPathBlock
noncomputable section
open Set Finset CandidateRootBudget CandidateBootstrapBudget CandidateCenterEndpointBudget
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

theorem horizon_eq : horizon=(4000:ℝ)*(Candidate.step:ℝ)+2*radius := by
  change (Candidate.parameters 2:ℝ)+2*radius=(4000:ℝ)*(Candidate.step:ℝ)+2*radius
  rw [full_nominal_time_exact]

theorem step_nonneg : 0≤(Candidate.step:ℝ) := Rat.cast_nonneg.mpr Candidate.positive_step.le
theorem local_cap : (Candidate.step:ℝ)+2*radius≤(UniversalMajorant.universalStepCap:ℝ) :=
  (candidate_extension_for_radius (r:=radius) le_rfl).1

variable {σ : ℝ} (hσ : |σ|≤1)
variable (A : PolynomialPointGridBlock σ (Candidate.step:ℝ) (1/10^55) (1/10^55) 4000)
variable (hstate : A.state 0=Candidate.initial) (hmatrix : A.matrix 0=1)

def grid (R : ℝ) (hR : 2400*R≤1/100) :=
  A.toExtendedGrid hσ (by norm_num) radius R step_nonneg radius_pos.le local_cap hR hmatrix

include hstate in
theorem grid_initial (R : ℝ) (hR : 2400*R≤1/100) :
    (grid hσ A hmatrix R hR).reference 0 0=Candidate.initial := by
  exact (A.extended_initial_reference hσ (by norm_num) radius R step_nonneg radius_pos.le
    local_cap hR hmatrix).trans hstate

theorem state_sum (R : ℝ) (hR : 2400*R≤1/100) :
    (∑j∈range 4000,(grid hσ A hmatrix R hR).stateJump j)≤stateResetBudget := by
  rw [grid,PolynomialPointGridBlock.extended_state_jump_sum]
  norm_num [stateResetBudget]

theorem matrix_sum (R : ℝ) (hR : 2400*R≤1/100) :
    (∑j∈range 4000,(grid hσ A hmatrix R hR).matrixJump j)≤matrixResetBudget := by
  rw [grid,PolynomialPointGridBlock.extended_matrix_jump_sum]
  norm_num [matrixResetBudget]

include A hstate hmatrix in
theorem actual_matrix_bounds :
    ActualFlowMatrixBounds σ hσ horizon Candidate.initial tubeRadius initialSet 8000 16000 := by
  have hR : 2400*uniformMetricRadius≤1/100 := by
    norm_num [uniformMetricRadius,radius,candidateWideTimeRadius]
  have h := @uniform_actual_matrix_bounds σ hσ 4000 (by norm_num)
  rw [horizon_eq] at h
  have hb := h (grid hσ A hmatrix uniformMetricRadius hR)
    (grid_initial hσ A hstate hmatrix _ hR)
    (state_sum hσ A hmatrix _ hR) (matrix_sum hσ A hmatrix _ hR)
  simpa only [←horizon_eq] using hb

include hstate hmatrix in
theorem actual_center_endpoints :
    ‖supportFlow σ hσ (Candidate.parameters 2:ℝ) Candidate.initial-A.state 4000‖≤endpointStateError ∧
    ‖fderiv ℝ (supportFlow σ hσ (Candidate.parameters 2:ℝ)) Candidate.initial-A.matrix 4000‖≤endpointMatrixError := by
  have hR : 2400*centerMetricRadius≤1/100 := by norm_num [centerMetricRadius]
  have ht := A.nominal_in_last_segment hσ (by norm_num) radius centerMetricRadius
    step_nonneg radius_pos.le local_cap hR hmatrix
  have h := @center_actual_errors σ hσ 4000 (by norm_num)
  rw [horizon_eq] at h
  have he := h (grid hσ A hmatrix centerMetricRadius hR)
    (grid_initial hσ A hstate hmatrix _ hR)
    (state_sum hσ A hmatrix _ hR) (matrix_sum hσ A hmatrix _ hR)
    (by norm_num : 3999<4000) ht
  have hx := A.nominal_state_comparison hσ (by norm_num) radius centerMetricRadius
    step_nonneg radius_pos.le local_cap hR hmatrix he.2.1
  have hp := A.nominal_matrix_comparison hσ (by norm_num) radius centerMetricRadius
    step_nonneg radius_pos.le local_cap hR hmatrix he.2.2
  constructor
  · simpa only [Nat.cast_ofNat,full_nominal_time_exact,endpointStateError] using hx
  · simpa only [Nat.cast_ofNat,full_nominal_time_exact,endpointMatrixError] using hp

end
end SolitonClassification.Rotating.FullPathBlock

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf (privateToUserName name) then
      for ax in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Full-path block bridge audit failed: {name} depends on {ax}"
      count := count+1
  logInfo m!"Full-path block endpoint bridge: {count} declarations; standard axioms only."
