import SolitonClassification.Rotating.Block8Grid
import SolitonClassification.Rotating.FlowMetricDeviationBootstrap
import SolitonClassification.Rotating.FlowMetricDeviationBudget

/-! True ODE/derivative consequences of all eight different finite leaves.
The theorem is only for the pilot horizon 8*h+2e-24. It does not assert the
full 4000-step trajectory or a shooting root. -/
namespace SolitonClassification.Rotating.Block8
noncomputable section
open Set Candidate
set_option Elab.async false
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def initialRadius : ℝ := 1/10^35
def relativeError : ℝ := 1/10^10

theorem forcing_eq : grid.forcing=
    5000*(2*2400^2*metricRadius^2+(4/10^16)*metricRadius+6/10^40) := rfl

theorem strict_budget :
    (initialRadius+grid.forcing*horizon+5000*jumpBudget)*Real.exp (5000*jumpBudget)<metricRadius := by
  have he : Real.exp (5000*jumpBudget)≤2 := by
    have h:=exp_deviation_budget (δrel:=(1:ℝ)) (by norm_num)
      (by norm_num [jumpBudget] : 5000*jumpBudget≤(1:ℝ)/(1+1))
    simpa only [show (1:ℝ)+1=2 by norm_num] using h
  have hf : 0≤grid.forcing := by rw [forcing_eq]; norm_num [metricRadius]
  have hp : 0 ≤ initialRadius+grid.forcing*horizon+5000*jumpBudget := by
    have ht:=horizon_bounds.1
    have hb : 0 ≤ initialRadius := by norm_num [initialRadius]
    have hj : 0≤jumpBudget := by norm_num [jumpBudget]
    positivity
  calc
    _ ≤ (initialRadius+grid.forcing*horizon+5000*jumpBudget)*2 := mul_le_mul_of_nonneg_left he hp
    _ ≤ (initialRadius+grid.forcing*1+5000*jumpBudget)*2 := by nlinarith [horizon_bounds.2]
    _ < metricRadius := by rw [forcing_eq]; norm_num [initialRadius,metricRadius,jumpBudget]

theorem deviation_budget :
    Real.exp (5000*(4*(2400*metricRadius)*2400+4/10^16)*horizon+5000*jumpBudget)≤1+relativeError := by
  apply exp_deviation_budget (by norm_num [relativeError])
  calc
    _ ≤ 5000*(4*(2400*metricRadius)*2400+4/10^16)*1+5000*jumpBudget := by
      gcongr
      · norm_num [metricRadius]
      · exact horizon_bounds.2
    _ ≤ relativeError/(1+relativeError) := by norm_num [metricRadius,jumpBudget,relativeError]

theorem initial_ball_budget : ‖initial-grid.reference 0 0‖+initialRadius ≤ initialRadius := by
  rw [initial_reference]; simp

theorem actual_on_segment {a : State} (ha : a∈Metric.ball initial initialRadius)
    {j : ℕ} (hj : j<8) {t : ℝ} (ht : t∈Icc (grid.time j) (grid.time (j+1))) :
    supportFlow 1 (by norm_num) t a∈outerTube ∧
      ‖supportFlow 1 (by norm_num) t a-grid.reference j t‖≤2400*metricRadius := by
  exact grid.actual_on_segment (by norm_num) a
    (by norm_num [initialRadius]) (by norm_num) (by norm_num) (by norm_num [metricRadius])
    (by norm_num) (by norm_num) state_jump_sum matrix_jump_sum strict_budget
    (grid.initial_error_of_ball initial_ball_budget ha) hj t ht

theorem actual_tube {a : State} (ha : a∈Metric.ball initial initialRadius)
    {t : ℝ} (ht : t∈Icc 0 horizon) : supportFlow 1 (by norm_num) t a∈outerTube :=
  grid.actual_mem_outerTube (by norm_num) a (by norm_num) (by norm_num [initialRadius])
    (by norm_num) (by norm_num) (by norm_num [metricRadius]) (by norm_num) (by norm_num)
    state_jump_sum matrix_jump_sum strict_budget (grid.initial_error_of_ball initial_ball_budget ha) t ht

theorem actual_original_derivative {a : State} (ha : a∈Metric.ball initial initialRadius)
    {t : ℝ} (ht : t∈Icc 0 horizon) :
    HasDerivAt (fun s=>supportFlow 1 (by norm_num) s a) (field (supportFlow 1 (by norm_num) t a)) t := by
  simpa only [one_smul] using supportFlow_original_derivative 1 (by norm_num) a t (actual_tube ha ht)

theorem actual_state_endpoint {a : State} (ha : a∈Metric.ball initial initialRadius) :
    ‖supportFlow 1 (by norm_num) nominalTime a-Block8Nodes.state 8‖≤3/10^29 := by
  have hx:=(actual_on_segment ha (by norm_num : 7<8) nominal_in_last_segment).2
  exact (nominal_state_comparison hx).trans (by norm_num [metricRadius])

theorem actual_matrix_endpoint {a : State} (ha : a∈Metric.ball initial initialRadius) :
    ‖fderiv ℝ (supportFlow 1 (by norm_num) nominalTime) a-Block8Nodes.operator 8‖≤3/10^7 := by
  have hP := grid.actualDeviation (by norm_num) (by norm_num) (by norm_num [initialRadius])
    (by norm_num) (by norm_num) (by norm_num [metricRadius]) (by norm_num) (by norm_num)
    state_jump_sum matrix_jump_sum strict_budget initial_ball_budget deviation_budget
    a ha 7 (by norm_num) nominalTime nominal_in_last_segment
  exact (nominal_matrix_comparison hP).trans (by norm_num [relativeError])

theorem center_ball : initial∈Metric.ball initial initialRadius := by
  simp only [Metric.mem_ball,dist_self]; norm_num [initialRadius]

theorem center_actual_state :
    ‖supportFlow 1 (by norm_num) nominalTime initial-Block8Nodes.state 8‖≤3/10^29 :=
  actual_state_endpoint center_ball

theorem center_actual_matrix :
    ‖fderiv ℝ (supportFlow 1 (by norm_num) nominalTime) initial-Block8Nodes.operator 8‖≤3/10^7 :=
  actual_matrix_endpoint center_ball

end
end SolitonClassification.Rotating.Block8

#print axioms SolitonClassification.Rotating.Block8.center_actual_state
#print axioms SolitonClassification.Rotating.Block8.center_actual_matrix

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
