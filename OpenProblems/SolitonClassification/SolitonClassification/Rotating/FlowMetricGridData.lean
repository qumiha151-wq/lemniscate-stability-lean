import SolitonClassification.Rotating.FlowMetricSegment
import SolitonClassification.Rotating.FlowMetricReset
import SolitonClassification.Rotating.FlowMetricDiscrete

/-! A finite reference grid with actual differential and error semantics.
State error and matrix residual are independent inputs; no Taylor order
is fixed. Exact local reference solutions are the residual-zero case.
All norms concern true real functions, not unverified numeric arrays. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Finset
open scoped Topology
set_option backward.isDefEq.respectTransparency false

structure FlowMetricGridData (σ : ℝ) (hσ : |σ|≤1) (a : State)
    (N : ℕ) (T K I E ρ : ℝ) where
  time : ℕ → ℝ
  matrix : ℕ → ℝ → FlowEnd
  reference : ℕ → ℝ → State
  residual : ℕ → ℝ → FlowEnd
  jump : ℕ → ℝ
  timeZero : time 0=0
  timeLast : time N=T
  timeMem : ∀j≤N,time j∈Icc 0 T
  timeStep : ∀j<N,time j≤time (j+1)
  matrixInitial : matrix 0 0=1
  nodeUnit : ∀j≤N,IsUnit (matrix j (time j))
  nodeInverseBound : ∀j≤N,‖Ring.inverse (matrix j (time j))‖≤I
  matrixContinuous : ∀j<N,ContinuousOn (matrix j) (Icc (time j) (time (j+1)))
  matrixUnit : ∀j<N,∀t∈Icc (time j) (time (j+1)),IsUnit (matrix j t)
  matrixDerivative : ∀j<N,∀t∈Ico (time j) (time (j+1)),
    HasDerivWithinAt (matrix j)
      ((σ • fderiv ℝ field (reference j t))*matrix j t+residual j t) (Ici t) t
  matrixBound : ∀j<N,∀t∈Icc (time j) (time (j+1)),‖matrix j t‖≤K
  inverseBound : ∀j<N,∀t∈Icc (time j) (time (j+1)),‖Ring.inverse (matrix j t)‖≤I
  referenceTube : ∀j<N,∀t∈Icc (time j) (time (j+1)),reference j t∈outerTube
  stateError : ∀j<N,∀t∈Icc (time j) (time (j+1)),‖supportFlow σ hσ t a-reference j t‖≤E
  residualBound : ∀j<N,∀t∈Icc (time j) (time (j+1)),‖residual j t‖≤ρ
  jumpNonneg : ∀j<N,0≤jump j
  resetBound : ∀j<N,‖matrix j (time (j+1))-matrix (j+1) (time (j+1))‖≤jump j

namespace FlowMetricGridData
variable {σ : ℝ} {hσ : |σ|≤1} {a : State} {N : ℕ} {T K I E ρ : ℝ}

def rate (_g : FlowMetricGridData σ hσ a N T K I E ρ) : ℝ := I*(4*E*K+ρ)
def duration (g : FlowMetricGridData σ hσ a N T K I E ρ) (j : ℕ) : ℝ := g.time (j+1)-g.time j
def forwardNode (g : FlowMetricGridData σ hσ a N T K I E ρ) (j : ℕ) : ℝ :=
  ‖flowMetricForward σ hσ a (g.matrix j) (g.time j)‖
def inverseNode (g : FlowMetricGridData σ hσ a N T K I E ρ) (j : ℕ) : ℝ :=
  ‖flowMetricInverse σ hσ a (g.matrix j) (g.time j)‖

theorem forwardNode_zero (g : FlowMetricGridData σ hσ a N T K I E ρ) : g.forwardNode 0=1 := by
  simp only [forwardNode,g.timeZero,flowMetricForward,g.matrixInitial,supportFlow_fderiv_initial]
  change ‖Ring.inverse (1:FlowEnd)*1‖=1
  simp only [Ring.inverse_one,one_mul,norm_one]

theorem inverseNode_zero (g : FlowMetricGridData σ hσ a N T K I E ρ) : g.inverseNode 0=1 := by
  simp only [inverseNode,g.timeZero,flowMetricInverse,g.matrixInitial,supportFlow_inverse_zero]
  change ‖(1:FlowEnd)*1‖=1
  simp only [one_mul,norm_one]

theorem segment_growth (g : FlowMetricGridData σ hσ a N T K I E ρ)
    {c : State} {R : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R) (ha : a∈Metric.ball c R)
    (hE : 0≤E) (hI : 0≤I) {j : ℕ} (hj : j<N) :
    ∀t∈Icc (g.time j) (g.time (j+1)),
      (‖flowMetricForward σ hσ a (g.matrix j) t‖≤g.forwardNode j*Real.exp (g.rate*(t-g.time j))) ∧
      (‖flowMetricInverse σ hσ a (g.matrix j) t‖≤g.inverseNode j*Real.exp (g.rate*(t-g.time j))) := by
  apply actual_metric_segment_growth σ hσ hreg ha (g.timeMem j (by omega)).1
    (g.timeMem (j+1) (by omega)).2 (g.matrixContinuous j hj) (g.matrixUnit j hj)
    (g.matrixDerivative j hj)
  intro t ht
  have ht' := Ico_subset_Icc_self ht
  have htT : t∈Icc 0 T := ⟨(g.timeMem j (by omega)).1.trans ht.1,
    ht.2.le.trans (g.timeMem (j+1) (by omega)).2⟩
  exact actual_flowMetricCoefficient_norm_bound σ hσ (hreg a ha t htT)
    (g.referenceTube j hj t ht') hE hI (g.stateError j hj t ht')
    (g.inverseBound j hj t ht') (g.matrixBound j hj t ht') (g.residualBound j hj t ht')

theorem forward_step (g : FlowMetricGridData σ hσ a N T K I E ρ)
    {c : State} {R : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R) (ha : a∈Metric.ball c R)
    (hE : 0≤E) (hI : 0≤I) {j : ℕ} (hj : j<N) :
    g.forwardNode (j+1)≤(1+I*g.jump j)*g.forwardNode j*Real.exp (g.rate*g.duration j) := by
  have hend : g.time (j+1)∈Icc (g.time j) (g.time (j+1)) := ⟨g.timeStep j hj,le_rfl⟩
  have hs := (g.segment_growth hreg ha hE hI hj (g.time (j+1)) hend).1
  have hr := metric_forward_reset_bound
    (P:=fderiv ℝ (supportFlow σ hσ (g.time (j+1))) a)
    (g.matrixUnit j hj _ hend) (g.nodeUnit (j+1) (by omega)) hI
    (g.nodeInverseBound (j+1) (by omega)) (g.resetBound j hj)
  change g.forwardNode (j+1)≤(1+I*g.jump j)*‖flowMetricForward σ hσ a (g.matrix j) (g.time (j+1))‖ at hr
  have hjn := g.jumpNonneg j hj
  exact hr.trans ((mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by dsimp [duration]; ring))

theorem inverse_step (g : FlowMetricGridData σ hσ a N T K I E ρ)
    {c : State} {R : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R) (ha : a∈Metric.ball c R)
    (hE : 0≤E) (hI : 0≤I) {j : ℕ} (hj : j<N) :
    g.inverseNode (j+1)≤(1+I*g.jump j)*g.inverseNode j*Real.exp (g.rate*g.duration j) := by
  have hend : g.time (j+1)∈Icc (g.time j) (g.time (j+1)) := ⟨g.timeStep j hj,le_rfl⟩
  have hs := (g.segment_growth hreg ha hE hI hj (g.time (j+1)) hend).2
  have hr := metric_inverse_reset_bound (Q:=supportFlowInverse σ hσ a (g.time (j+1)))
    (g.matrixUnit j hj _ hend) hI (g.inverseBound j hj _ hend) (g.resetBound j hj)
  change g.inverseNode (j+1)≤(1+I*g.jump j)*‖flowMetricInverse σ hσ a (g.matrix j) (g.time (j+1))‖ at hr
  have hjn := g.jumpNonneg j hj
  exact hr.trans ((mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by dsimp [duration]; ring))

end FlowMetricGridData
end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating actual matrix-grid data audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating actual matrix-grid data audit passed for {count} declarations."
