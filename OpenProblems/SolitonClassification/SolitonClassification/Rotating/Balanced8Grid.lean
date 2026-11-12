import SolitonClassification.Rotating.Balanced8Left4
import SolitonClassification.Rotating.Balanced8Right4
import SolitonClassification.Rotating.PolynomialPointGridBlockGrid
import SolitonClassification.Rotating.RotatingGridHorizonCandidate

/-! Exact state and full-matrix seam, followed by the genuine point-block
append theorem. This source does not import the flat Block8Grid proof. -/
namespace SolitonClassification.Rotating.Balanced8
noncomputable section
open Set Finset Candidate UniversalMajorant
set_option Elab.async false
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem state_seam : Balanced8Left4.certificate.state 4=Balanced8Right4.certificate.state 0 := by
  rw [Balanced8Left4.state_last,Balanced8Right4.state_start]
theorem matrix_seam : Balanced8Left4.certificate.matrix 4=Balanced8Right4.certificate.matrix 0 := by
  rw [Balanced8Left4.matrix_last,Balanced8Right4.matrix_start]

def certificate : PolynomialPointGridBlock 1 (step:ℝ) (1/10^55) (1/10^55) 8 :=
  PolynomialPointGridBlock.append Balanced8Left4.certificate Balanced8Right4.certificate state_seam matrix_seam

theorem state_start : certificate.state 0=initial := by
  rw [certificate,PolynomialPointGridBlock.append_state_zero,Balanced8Left4.state_start,Block8Nodes.state_zero]
theorem matrix_start : certificate.matrix 0=1 := by
  rw [certificate,PolynomialPointGridBlock.append_matrix_zero,Balanced8Left4.matrix_start,Block8Nodes.operator_initial]
theorem state_last : certificate.state 8=Block8Nodes.state 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).state (4+4)=_
  rw [PolynomialPointGridBlock.append_state_last,Balanced8Right4.state_last]
theorem matrix_last : certificate.matrix 8=Block8Nodes.operator 8 := by
  change (PolynomialPointGridBlock.append _ _ state_seam matrix_seam).matrix (4+4)=_
  rw [PolynomialPointGridBlock.append_matrix_last,Balanced8Right4.matrix_last]

attribute [irreducible] certificate

def radius : ℝ := (candidateWideTimeRadius:ℝ)
def nominalTime : ℝ := 8*(step:ℝ)
def horizon : ℝ := 8*(step:ℝ)+2*radius
def metricRadius : ℝ := 1/10^32
def jumpBudget : ℝ := 7/10^55

theorem radius_nonneg : 0≤radius := candidate_wide_time_radius_pos.le
theorem step_nonneg : 0≤(step:ℝ) := Rat.cast_nonneg.mpr positive_step.le
theorem local_cap : (step:ℝ)+2*radius≤(universalStepCap:ℝ) :=
  (candidate_extension_for_radius (r:=radius) le_rfl).1
theorem horizon_bounds : 0≤horizon ∧ horizon≤1 := by
  have hcap := local_cap
  have hr := radius_nonneg
  have hs := step_nonneg
  have hnum : (universalStepCap:ℝ)≤1/100 := by norm_num [universalStepCap]
  constructor
  · dsimp [horizon]; positivity
  · dsimp [horizon]; linarith

def grid : FlowBootstrapGridData 1 8 horizon 2400 5000 metricRadius (4/10^16) (6/10^40) :=
  certificate.toExtendedGrid (by norm_num) (by norm_num) radius metricRadius step_nonneg radius_nonneg
    local_cap (by norm_num [metricRadius]) matrix_start

theorem initial_reference : grid.reference 0 0=initial := by
  rw [grid,PolynomialPointGridBlock.extended_initial_reference,state_start]
theorem state_jump_sum : (∑j∈range 8,grid.stateJump j)≤jumpBudget := by
  rw [grid,PolynomialPointGridBlock.extended_state_jump_sum]
  norm_num [jumpBudget]
theorem matrix_jump_sum : (∑j∈range 8,grid.matrixJump j)≤jumpBudget := by
  rw [grid,PolynomialPointGridBlock.extended_matrix_jump_sum]
  norm_num [jumpBudget]
theorem last_state_jump : grid.stateJump 7=0 := rfl
theorem last_matrix_jump : grid.matrixJump 7=0 := rfl

theorem nominal_in_last_segment : nominalTime∈Icc (grid.time 7) (grid.time 8) := by
  exact center_endpoint_in_extended_last_segment (N:=8) (by norm_num) step_nonneg radius_nonneg

theorem nominal_state_comparison {x : State} {E : ℝ}
    (hx : ‖x-grid.reference 7 nominalTime‖≤E) : ‖x-Block8Nodes.state 8‖≤E+1/10^55 := by
  have h := certificate.nominal_state_comparison (by norm_num) (by norm_num) radius metricRadius
    step_nonneg radius_nonneg local_cap (by norm_num [metricRadius]) matrix_start hx
  rwa [state_last] at h
theorem nominal_matrix_comparison {P : FlowEnd} {E : ℝ}
    (hP : ‖P-grid.matrix 7 nominalTime‖≤E) : ‖P-Block8Nodes.operator 8‖≤E+1/10^55 := by
  have h := certificate.nominal_matrix_comparison (by norm_num) (by norm_num) radius metricRadius
    step_nonneg radius_nonneg local_cap (by norm_num [metricRadius]) matrix_start hP
  rwa [matrix_last] at h

end
end SolitonClassification.Rotating.Balanced8
#print axioms SolitonClassification.Rotating.Balanced8.grid

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for ax in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Balanced pilot audit failed: {name} depends on {ax}"
      count := count+1
  logInfo m!"Balanced pilot audited: {count} declarations; standard axioms only."
