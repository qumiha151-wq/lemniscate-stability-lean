import SolitonClassification.Rotating.TwoSegmentGrid
import SolitonClassification.Rotating.FlowMetricDeviationBootstrap
import SolitonClassification.Rotating.FlowMetricDeviationBudget

/-! An actual two-segment result: the chosen global ODE trajectory,
its full initial derivative, both resets and the true polynomial tails.
The small initial ball is also constructed from the strict bootstrap,
rather than assuming that the actual flow remains in the tube. -/
namespace SolitonClassification.Rotating.GridReset
noncomputable section
open Set Candidate
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

theorem two_horizon_bound : 0≤2*(step:ℝ) ∧ 2*(step:ℝ)≤2/125 := by
  have h0 : 0≤(step:ℝ) := Rat.cast_nonneg.mpr positive_step.le
  have h1 : (step:ℝ)≤1/125 := by
    have h : step≤1/125 := (step_below_cap.trans cap_below_local_time).le
    have hc : (step:ℝ)≤((1/125:ℚ):ℝ) := Rat.cast_le.mpr h
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hc
  constructor <;> linarith

theorem two_forcing : twoSegmentGrid.forcing=
    3*(2*3^2*(1/10^54)^2+(4/10^19)*(1/10^54)+1/10^57) := rfl

theorem two_strict_budget :
    ((1:ℝ)/10^55+twoSegmentGrid.forcing*(2*(step:ℝ))+3*(2/10^57))*
      Real.exp (3*(2/10^57))<1/10^54 := by
  have he : Real.exp ((3:ℝ)*(2/10^57))≤2 := by
    have h := exp_deviation_budget (δrel:=(1:ℝ)) (by norm_num)
      (by norm_num : (3:ℝ)*(2/10^57)≤1/(1+1))
    simpa only [show (1:ℝ)+1=2 by norm_num] using h
  have hf : 0≤twoSegmentGrid.forcing := by rw [two_forcing]; positivity
  have hp : 0≤(1:ℝ)/10^55+twoSegmentGrid.forcing*(2*(step:ℝ))+3*(2/10^57) :=
    by have ht:=two_horizon_bound.1; positivity
  calc
    _ ≤ ((1:ℝ)/10^55+twoSegmentGrid.forcing*(2*(step:ℝ))+3*(2/10^57))*2 :=
      mul_le_mul_of_nonneg_left he hp
    _ ≤ ((1:ℝ)/10^55+twoSegmentGrid.forcing*(2/125)+3*(2/10^57))*2 := by
      nlinarith [two_horizon_bound.2]
    _ < 1/10^54 := by rw [two_forcing]; norm_num

theorem two_deviation_budget :
    Real.exp (3*(4*(3*((1:ℝ)/10^54))*3+4/10^19)*(2*(step:ℝ))+3*(2/10^57))≤1+1/10^19 := by
  apply exp_deviation_budget (by positivity)
  calc
    _ ≤ 3*(4*(3*((1:ℝ)/10^54))*3+4/10^19)*(2/125)+3*(2/10^57) := by
      gcongr
      exact two_horizon_bound.2
    _ ≤ ((1:ℝ)/10^19)/(1+1/10^19) := by norm_num

theorem two_initial_ball_budget :
    ‖initial-twoSegmentGrid.reference 0 0‖+(1:ℝ)/10^55≤1/10^55 := by
  rw [two_initial_reference]
  simp

theorem two_actual_on_segment {a : State} (ha : a∈Metric.ball initial ((1:ℝ)/10^55))
    {j : ℕ} (hj : j<2) {t : ℝ} (ht : t∈Icc (twoSegmentGrid.time j) (twoSegmentGrid.time (j+1))) :
    supportFlow 1 (by norm_num) t a∈outerTube ∧
      ‖supportFlow 1 (by norm_num) t a-twoSegmentGrid.reference j t‖≤3/10^54 := by
  have hinit:=twoSegmentGrid.initial_error_of_ball two_initial_ball_budget ha
  have h:=twoSegmentGrid.actual_on_segment (by norm_num) a
    (by positivity) (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity)
    two_state_jump_sum two_matrix_jump_sum two_strict_budget hinit hj t ht
  simpa only [div_eq_mul_inv,one_mul] using h

theorem two_actual_tube {a : State} (ha : a∈Metric.ball initial ((1:ℝ)/10^55))
    {t : ℝ} (ht : t∈Icc 0 (2*(step:ℝ))) : supportFlow 1 (by norm_num) t a∈outerTube := by
  exact twoSegmentGrid.actual_mem_outerTube (by norm_num) a (by norm_num)
    (by positivity) (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity)
    two_state_jump_sum two_matrix_jump_sum two_strict_budget
    (twoSegmentGrid.initial_error_of_ball two_initial_ball_budget ha) t ht

theorem two_actual_original_derivative {a : State} (ha : a∈Metric.ball initial ((1:ℝ)/10^55))
    {t : ℝ} (ht : t∈Icc 0 (2*(step:ℝ))) :
    HasDerivAt (fun s=>supportFlow 1 (by norm_num) s a)
      (field (supportFlow 1 (by norm_num) t a)) t := by
  simpa only [one_smul] using supportFlow_original_derivative 1 (by norm_num) a t (two_actual_tube ha ht)

theorem two_actual_state_endpoint {a : State} (ha : a∈Metric.ball initial ((1:ℝ)/10^55)) :
    ‖supportFlow 1 (by norm_num) (2*(step:ℝ)) a-state2‖≤4/10^54 := by
  have ht : 2*(step:ℝ)∈Icc (twoSegmentGrid.time 1) (twoSegmentGrid.time (1+1)) := by
    rw [two_time,two_time]
    have hs : 0≤(step:ℝ) := Rat.cast_nonneg.mpr positive_step.le
    constructor
    · norm_num
      linarith
    · norm_num
  have he:=(two_actual_on_segment ha (by norm_num : 1<2) ht).2
  have hr:=twoSegmentGrid.stateReset 1 (by norm_num)
  have ht2 : twoSegmentGrid.time (1+1)=2*(step:ℝ) := two_time 2
  rw [ht2,two_terminal_reference] at hr
  have hr' : ‖twoSegmentGrid.reference 1 (2*(step:ℝ))-state2‖≤(1:ℝ)/10^57 := hr
  calc
    _ = ‖(supportFlow 1 (by norm_num) (2*(step:ℝ)) a-twoSegmentGrid.reference 1 (2*(step:ℝ)))+
        (twoSegmentGrid.reference 1 (2*(step:ℝ))-state2)‖ := by congr 1; abel
    _ ≤ ‖supportFlow 1 (by norm_num) (2*(step:ℝ)) a-twoSegmentGrid.reference 1 (2*(step:ℝ))‖+
        ‖twoSegmentGrid.reference 1 (2*(step:ℝ))-state2‖ := norm_add_le _ _
    _ ≤ 3/10^54+1/10^57 := add_le_add he hr'
    _ ≤ 4/10^54 := by norm_num

theorem two_actual_matrix_endpoint {a : State} (ha : a∈Metric.ball initial ((1:ℝ)/10^55)) :
    ‖fderiv ℝ (supportFlow 1 (by norm_num) (2*(step:ℝ))) a-matrix2‖≤4/10^19 := by
  have h := twoSegmentGrid.actualDeviation_terminal (by norm_num)
    (by norm_num) (by positivity) (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity)
    two_state_jump_sum two_matrix_jump_sum two_strict_budget two_initial_ball_budget two_deviation_budget a ha
  rw [two_terminal_matrix] at h
  change ‖fderiv ℝ (supportFlow 1 _ (2*(step:ℝ))) a-matrix2‖≤
    (3+(1:ℝ)/10^57)*((1:ℝ)/10^19) at h
  exact h.trans (by norm_num)

theorem two_center_ball : initial∈Metric.ball initial ((1:ℝ)/10^55) := by
  simp only [Metric.mem_ball,dist_self]
  positivity

theorem two_center_actual_state : ‖supportFlow 1 (by norm_num) (2*(step:ℝ)) initial-state2‖≤4/10^54 :=
  two_actual_state_endpoint two_center_ball

theorem two_center_actual_matrix :
    ‖fderiv ℝ (supportFlow 1 (by norm_num) (2*(step:ℝ))) initial-matrix2‖≤4/10^19 :=
  two_actual_matrix_endpoint two_center_ball

end
end SolitonClassification.Rotating.GridReset

#print axioms SolitonClassification.Rotating.GridReset.two_center_actual_state
#print axioms SolitonClassification.Rotating.GridReset.two_center_actual_matrix
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Actual two-segment state/full-matrix bootstrap audited for {count} declarations."
