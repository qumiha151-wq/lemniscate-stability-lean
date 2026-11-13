module

public import SolitonClassification.Rotating.CandidateRootBudget
public import SolitonClassification.Rotating.FlowMetricDeviationBootstrap
public import SolitonClassification.Rotating.FlowMetricDeviationBudget

@[expose] public section

/-! Fixed analytic budgets for the actual candidate horizon. Concrete
reference grids, their initial value and finite reset sums remain inputs.
Center accuracy and the larger parameter neighborhood are kept separate. -/
namespace SolitonClassification.Rotating.CandidateBootstrapBudget
noncomputable section
open Set Finset CandidateRootBudget
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

def stateResetBudget : ℝ := 1/10^48
def matrixResetBudget : ℝ := 1/10^40
def matrixResidualBudget : ℝ := 4/10^16
def stateResidualBudget : ℝ := 6/10^40
def uniformMetricRadius : ℝ := 16*radius
def centerMetricRadius : ℝ := 1/10^32
def centerInitialRadius : ℝ := 1/10^35
def centerRelativeError : ℝ := 1/10^10
def forcing (R : ℝ) : ℝ :=
  5000*(2*2400^2*R^2+matrixResidualBudget*R+stateResidualBudget)

theorem reset_exponential : Real.exp (5000*matrixResetBudget)≤3/2 := by
  have h:=exp_deviation_budget (δrel:=(1:ℝ)/2) (by norm_num)
    (by norm_num [matrixResetBudget] : 5000*matrixResetBudget≤((1:ℝ)/2)/(1+1/2))
  norm_num at h ⊢
  exact h

theorem strict_budget_of_rational {B R : ℝ}
    (hB : 0≤B) (hF : 0≤forcing R)
    (hfinite : (B+forcing R*32+5000*stateResetBudget)*(3/2)<R) :
    (B+forcing R*horizon+5000*stateResetBudget)*Real.exp (5000*matrixResetBudget)<R := by
  have hpoly : B+forcing R*horizon+5000*stateResetBudget≤B+forcing R*32+5000*stateResetBudget := by
    nlinarith [horizon_bounds.2]
  have hupper : 0≤B+forcing R*32+5000*stateResetBudget := by
    have hS : 0≤stateResetBudget := by norm_num [stateResetBudget]
    positivity
  exact (mul_le_mul hpoly reset_exponential (Real.exp_pos _).le hupper).trans_lt hfinite

theorem uniform_strict_budget :
    (tubeRadius+forcing uniformMetricRadius*horizon+5000*stateResetBudget)*
      Real.exp (5000*matrixResetBudget)<uniformMetricRadius := by
  apply strict_budget_of_rational
  · have hr:=radius_pos; dsimp [tubeRadius]; positivity
  · norm_num [forcing,uniformMetricRadius,radius,candidateWideTimeRadius,
      matrixResidualBudget,stateResidualBudget]
  · norm_num [forcing,uniformMetricRadius,tubeRadius,radius,candidateWideTimeRadius,
      matrixResidualBudget,stateResidualBudget,stateResetBudget]

theorem center_strict_budget :
    (centerInitialRadius+forcing centerMetricRadius*horizon+5000*stateResetBudget)*
      Real.exp (5000*matrixResetBudget)<centerMetricRadius := by
  apply strict_budget_of_rational
  · norm_num [centerInitialRadius]
  · norm_num [forcing,centerMetricRadius,matrixResidualBudget,stateResidualBudget]
  · norm_num [forcing,centerMetricRadius,centerInitialRadius,
      matrixResidualBudget,stateResidualBudget,stateResetBudget]

theorem matrix_exponent_le {R : ℝ} (hR : 0≤R) :
    5000*(4*(2400*R)*2400+matrixResidualBudget)*horizon+5000*matrixResetBudget≤
      5000*(4*(2400*R)*2400+matrixResidualBudget)*32+5000*matrixResetBudget := by
  have hρ : 0≤matrixResidualBudget := by norm_num [matrixResidualBudget]
  have hc : 0≤5000*(4*(2400*R)*2400+matrixResidualBudget) := by positivity
  nlinarith [horizon_bounds.2]

theorem uniform_matrix_budget :
    Real.exp (5000*(4*(2400*uniformMetricRadius)*2400+matrixResidualBudget)*horizon+
      5000*matrixResetBudget)≤2 := by
  have h:=exp_deviation_budget (δrel:=(1:ℝ)) (by norm_num)
    ((matrix_exponent_le (R:=uniformMetricRadius)
      (by have hr:=radius_pos; dsimp [uniformMetricRadius]; positivity)).trans
      (by norm_num [uniformMetricRadius,radius,candidateWideTimeRadius,
        matrixResidualBudget,matrixResetBudget]))
  simpa only [show (1:ℝ)+1=2 by norm_num] using h

theorem center_matrix_budget :
    Real.exp (5000*(4*(2400*centerMetricRadius)*2400+matrixResidualBudget)*horizon+
      5000*matrixResetBudget)≤1+centerRelativeError := by
  apply exp_deviation_budget (by norm_num [centerRelativeError])
  exact (matrix_exponent_le (R:=centerMetricRadius) (by norm_num [centerMetricRadius])).trans
    (by norm_num [centerMetricRadius,centerRelativeError,matrixResidualBudget,matrixResetBudget])

theorem uniform_actual_matrix_bounds {σ : ℝ} (hσ : |σ|≤1) {N : ℕ} (hN : 0<N)
    (g : FlowBootstrapGridData σ N horizon 2400 5000 uniformMetricRadius matrixResidualBudget stateResidualBudget)
    (hinit : g.reference 0 0=Candidate.initial)
    (hSX : (∑j∈range N,g.stateJump j)≤stateResetBudget)
    (hSM : (∑j∈range N,g.matrixJump j)≤matrixResetBudget) :
    ActualFlowMatrixBounds σ hσ horizon Candidate.initial tubeRadius initialSet 8000 16000 := by
  have hcenter : ‖Candidate.initial-g.reference 0 0‖+tubeRadius≤tubeRadius := by rw [hinit]; simp
  have hsub : initialSet⊆Metric.ball Candidate.initial tubeRadius := by
    intro a ha
    have hh:=initial_set_inside_quarter_tube ha
    change dist a Candidate.initial<tubeRadius/4 at hh
    change dist a Candidate.initial<tubeRadius
    have hR : 0<tubeRadius := by have hr:=radius_pos; dsimp [tubeRadius]; positivity
    linarith
  have hG := g.actualMatrixBounds hσ hN
    (by have hr:=radius_pos; dsimp [tubeRadius]; positivity)
    (by norm_num) (by norm_num)
    (by have hr:=radius_pos; dsimp [uniformMetricRadius]; positivity)
    (by norm_num [matrixResidualBudget]) (by norm_num [stateResidualBudget])
    hSX hSM uniform_strict_budget hcenter hsub uniform_matrix_budget
  refine ⟨hG.tube,?_,?_⟩
  · intro a ha t ht
    exact (hG.derivativeBound a ha t ht).trans (by norm_num)
  · intro a ha t ht
    exact (hG.inverseBound a ha t ht).trans (by norm_num)

theorem center_actual_errors {σ : ℝ} (hσ : |σ|≤1) {N : ℕ} (hN : 0<N)
    (g : FlowBootstrapGridData σ N horizon 2400 5000 centerMetricRadius matrixResidualBudget stateResidualBudget)
    (hinit : g.reference 0 0=Candidate.initial)
    (hSX : (∑j∈range N,g.stateJump j)≤stateResetBudget)
    (hSM : (∑j∈range N,g.matrixJump j)≤matrixResetBudget)
    {j : ℕ} (hj : j<N) {t : ℝ} (ht : t∈Icc (g.time j) (g.time (j+1))) :
    supportFlow σ hσ t Candidate.initial∈outerTube ∧
      ‖supportFlow σ hσ t Candidate.initial-g.reference j t‖≤2400*centerMetricRadius ∧
      ‖fderiv ℝ (supportFlow σ hσ t) Candidate.initial-g.matrix j t‖≤2400*centerRelativeError := by
  have hcenter : ‖Candidate.initial-g.reference 0 0‖+centerInitialRadius≤centerInitialRadius := by
    rw [hinit];simp
  have hin : Candidate.initial∈Metric.ball Candidate.initial centerInitialRadius := by
    simp only [Metric.mem_ball,dist_self];norm_num [centerInitialRadius]
  have hX := g.actual_on_segment hσ Candidate.initial
    (by norm_num [centerInitialRadius]) (by norm_num) (by norm_num)
    (by norm_num [centerMetricRadius]) (by norm_num [matrixResidualBudget])
    (by norm_num [stateResidualBudget]) hSX hSM center_strict_budget
    (g.initial_error_of_ball hcenter hin) hj t ht
  have hP := g.actualDeviation hσ hN (by norm_num [centerInitialRadius])
    (by norm_num) (by norm_num) (by norm_num [centerMetricRadius])
    (by norm_num [matrixResidualBudget]) (by norm_num [stateResidualBudget])
    hSX hSM center_strict_budget hcenter center_matrix_budget Candidate.initial hin j hj t ht
  exact ⟨hX.1,hX.2,hP⟩

end
end SolitonClassification.Rotating.CandidateBootstrapBudget

#print axioms SolitonClassification.Rotating.CandidateBootstrapBudget.uniform_actual_matrix_bounds
#print axioms SolitonClassification.Rotating.CandidateBootstrapBudget.center_actual_errors
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Candidate bootstrap budget audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Candidate actual center/neighborhood bootstrap audited: {count} declarations; standard axioms only."
