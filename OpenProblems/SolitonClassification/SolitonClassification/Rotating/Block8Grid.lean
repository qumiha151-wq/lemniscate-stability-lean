import SolitonClassification.Rotating.Block8Leaf00
import SolitonClassification.Rotating.Block8Leaf01Matrix
import SolitonClassification.Rotating.Block8Leaf02Matrix
import SolitonClassification.Rotating.Block8Leaf03Matrix
import SolitonClassification.Rotating.Block8Leaf04Matrix
import SolitonClassification.Rotating.Block8Leaf05Matrix
import SolitonClassification.Rotating.Block8Leaf06Matrix
import SolitonClassification.Rotating.Block8Leaf07Matrix
import SolitonClassification.Rotating.ExtendedPolynomialGridEndpoints42
import SolitonClassification.Rotating.RotatingGridHorizonCandidate

/-! Eight different actual positive-time leaves. Internal jumps come from
kernel-checked finite recurrences. The extended terminal is the last
polynomial's actual value, so its reset is zero. The nominal eighth node is
used only in the separately charged original-endpoint comparison. -/
namespace SolitonClassification.Rotating.Block8
noncomputable section
open Set Finset Candidate UniversalMajorant
set_option Elab.async false
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

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

theorem state_reset (j : ℕ) (hj : j<8) :
    ‖polynomialPath (taylorPolynomial (Block8Nodes.state j) 42) (1*(step:ℝ))-
      Block8Nodes.state (j+1)‖≤1/10^55 := by
  interval_cases j
  · simpa only [one_mul] using Block8Leaf00.state_reset
  · simpa only [one_mul] using Block8Leaf01State.state_reset
  · simpa only [one_mul] using Block8Leaf02State.state_reset
  · simpa only [one_mul] using Block8Leaf03State.state_reset
  · simpa only [one_mul] using Block8Leaf04State.state_reset
  · simpa only [one_mul] using Block8Leaf05State.state_reset
  · simpa only [one_mul] using Block8Leaf06State.state_reset
  · simpa only [one_mul] using Block8Leaf07State.state_reset

theorem matrix_reset (j : ℕ) (hj : j<8) :
    ‖referencePolynomialMatrix 1 (Block8Nodes.state j) 22 (Block8Nodes.operator j) (step:ℝ)-
      Block8Nodes.operator (j+1)‖≤1/10^55 := by
  interval_cases j
  · exact Block8Leaf00.matrix_reset
  · exact Block8Leaf01Matrix.matrix_reset
  · exact Block8Leaf02Matrix.matrix_reset
  · exact Block8Leaf03Matrix.matrix_reset
  · exact Block8Leaf04Matrix.matrix_reset
  · exact Block8Leaf05Matrix.matrix_reset
  · exact Block8Leaf06Matrix.matrix_reset
  · exact Block8Leaf07Matrix.matrix_reset

def grid : FlowBootstrapGridData 1 8 horizon 2400 5000 metricRadius (4/10^16) (6/10^40) :=
  extendedPolynomialGrid42 1 (by norm_num) 8 (by norm_num) (step:ℝ) radius metricRadius
    Block8Nodes.state Block8Nodes.operator (fun _=>1/10^55) (fun _=>1/10^55)
    step_nonneg radius_nonneg local_cap (by norm_num [metricRadius])
    (fun j hj=>Block8Nodes.inner j (by omega)) Block8Nodes.operator_initial
    (fun j hj=>(Block8Nodes.bounds j (by omega)).2.1)
    (fun j hj=>(Block8Nodes.bounds j (by omega)).1)
    (fun j hj=>(Block8Nodes.bounds j (by omega)).2.2)
    (by intros; positivity) (by intros; positivity)
    (fun j hj=>state_reset j (by omega)) (fun j hj=>matrix_reset j (by omega))

theorem initial_reference : grid.reference 0 0=initial := by
  change extendedPolynomialState42 1 Block8Nodes.state 8 (step:ℝ) radius 0 0=initial
  rw [extendedPolynomialState42_before 1 Block8Nodes.state (by norm_num : 0<8)]
  simpa only [Nat.cast_zero,zero_mul,shiftedPolynomialState_zero] using Block8Nodes.state_zero

theorem state_jump_sum : (∑j∈range 8,grid.stateJump j)≤jumpBudget := by
  change (∑j∈range 8,if j+1<8 then (1:ℝ)/10^55 else 0)≤jumpBudget
  rw [internal_reset_sum (by norm_num : 0<8)]
  norm_num [jumpBudget]

theorem matrix_jump_sum : (∑j∈range 8,grid.matrixJump j)≤jumpBudget := by
  change (∑j∈range 8,if j+1<8 then (1:ℝ)/10^55 else 0)≤jumpBudget
  rw [internal_reset_sum (by norm_num : 0<8)]
  norm_num [jumpBudget]

theorem last_state_jump : grid.stateJump 7=0 := rfl
theorem last_matrix_jump : grid.matrixJump 7=0 := rfl

theorem nominal_in_last_segment : nominalTime∈Icc (grid.time 7) (grid.time 8) := by
  exact center_endpoint_in_extended_last_segment (N:=8) (by norm_num) step_nonneg radius_nonneg

theorem nominal_state_comparison {x : State} {E : ℝ}
    (hx : ‖x-grid.reference 7 nominalTime‖≤E) :
    ‖x-Block8Nodes.state 8‖≤E+1/10^55 := by
  exact extendedPolynomialState42_center_comparison 1 Block8Nodes.state (N:=8)
    (by norm_num) (step:ℝ) radius hx (state_reset 7 (by norm_num))

theorem nominal_matrix_comparison {P : FlowEnd} {E : ℝ}
    (hP : ‖P-grid.matrix 7 nominalTime‖≤E) :
    ‖P-Block8Nodes.operator 8‖≤E+1/10^55 := by
  exact extendedPolynomialMatrix22_center_comparison 1 Block8Nodes.state Block8Nodes.operator (N:=8)
    (by norm_num) (step:ℝ) radius hP (matrix_reset 7 (by norm_num))

end
end SolitonClassification.Rotating.Block8

#print axioms SolitonClassification.Rotating.Block8.grid

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for ax in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Eight-leaf concrete assembly audit failed: {name} depends on {ax}"
      count := count+1
  logInfo m!"Eight-leaf concrete assembly audited: {count} declarations; standard axioms only."
