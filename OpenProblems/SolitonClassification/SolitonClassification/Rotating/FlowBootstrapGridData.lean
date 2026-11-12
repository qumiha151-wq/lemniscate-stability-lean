import SolitonClassification.Rotating.FlowBootstrapSegment
import SolitonClassification.Rotating.FlowBootstrapReset
import SolitonClassification.Rotating.FlowBootstrapBudget
import SolitonClassification.Rotating.FlowMetricGlobal

/-! Reference data for a noncircular state/tube bootstrap. The reference
state and matrix are real functions with actual differential residuals.
Neither the actual trajectory's tube membership nor its error appears
as an input. State and matrix residuals may use different Taylor orders. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Finset
set_option backward.isDefEq.respectTransparency false

structure FlowBootstrapGridData (σ : ℝ) (N : ℕ) (T K I R ρ δ : ℝ) where
  time : ℕ → ℝ
  matrix : ℕ → ℝ → FlowEnd
  reference : ℕ → ℝ → State
  matrixResidual : ℕ → ℝ → FlowEnd
  stateResidual : ℕ → ℝ → State
  matrixJump : ℕ → ℝ
  stateJump : ℕ → ℝ
  timeZero : time 0=0
  timeLast : time N=T
  timeMem : ∀j≤N,time j∈Icc 0 T
  timeStep : ∀j<N,time j≤time (j+1)
  matrixInitial : matrix 0 0=1
  nodeUnit : ∀j≤N,IsUnit (matrix j (time j))
  nodeInverseBound : ∀j≤N,‖Ring.inverse (matrix j (time j))‖≤I
  matrixContinuous : ∀j<N,ContinuousOn (matrix j) (Icc (time j) (time (j+1)))
  referenceContinuous : ∀j<N,ContinuousOn (reference j) (Icc (time j) (time (j+1)))
  matrixUnit : ∀j<N,∀t∈Icc (time j) (time (j+1)),IsUnit (matrix j t)
  matrixDerivative : ∀j<N,∀t∈Ico (time j) (time (j+1)),
    HasDerivWithinAt (matrix j)
      ((σ • fderiv ℝ field (reference j t))*matrix j t+matrixResidual j t) (Ici t) t
  referenceDerivative : ∀j<N,∀t∈Ico (time j) (time (j+1)),
    HasDerivWithinAt (reference j) (σ • field (reference j t)+stateResidual j t) (Ici t) t
  matrixBound : ∀j<N,∀t∈Icc (time j) (time (j+1)),‖matrix j t‖≤K
  inverseBound : ∀j<N,∀t∈Icc (time j) (time (j+1)),‖Ring.inverse (matrix j t)‖≤I
  matrixResidualBound : ∀j<N,∀t∈Icc (time j) (time (j+1)),‖matrixResidual j t‖≤ρ
  stateResidualBound : ∀j<N,∀t∈Icc (time j) (time (j+1)),‖stateResidual j t‖≤δ
  referenceMargin : ∀j<N,∀t∈Icc (time j) (time (j+1)),outerTubeMargin (reference j t) (K*R)
  matrixJumpNonneg : ∀j<N,0≤matrixJump j
  stateJumpNonneg : ∀j<N,0≤stateJump j
  matrixReset : ∀j<N,‖matrix j (time (j+1))-matrix (j+1) (time (j+1))‖≤matrixJump j
  stateReset : ∀j<N,‖reference j (time (j+1))-reference (j+1) (time (j+1))‖≤stateJump j

namespace FlowBootstrapGridData
variable {σ : ℝ} {N : ℕ} {T K I R ρ δ : ℝ}

def duration (g : FlowBootstrapGridData σ N T K I R ρ δ) (j : ℕ) : ℝ := g.time (j+1)-g.time j
def forcing (_g : FlowBootstrapGridData σ N T K I R ρ δ) : ℝ := bootstrapForcing K I R ρ δ
def budget (g : FlowBootstrapGridData σ N T K I R ρ δ) (B : ℝ) : ℕ → ℝ :=
  bootstrapNodeBudget B g.forcing I g.duration g.stateJump g.matrixJump
def nodeError (g : FlowBootstrapGridData σ N T K I R ρ δ) (hσ : |σ|≤1) (a : State) (j : ℕ) : ℝ :=
  ‖bootstrapError σ hσ a (g.reference j) (g.matrix j) (g.time j)‖

theorem duration_nonneg (g : FlowBootstrapGridData σ N T K I R ρ δ) {j : ℕ} (hj : j<N) :
    0≤g.duration j := sub_nonneg.mpr (g.timeStep j hj)

theorem duration_sum (g : FlowBootstrapGridData σ N T K I R ρ δ) (n : ℕ) :
    (∑j∈range n,g.duration j)=g.time n := by
  induction n with
  | zero => simp [g.timeZero]
  | succ n ih => rw [sum_range_succ,ih,duration]; ring

theorem forcing_nonneg (g : FlowBootstrapGridData σ N T K I R ρ δ)
    (hI : 0≤I) (hR : 0≤R) (hρ : 0≤ρ) (hδ : 0≤δ) : 0≤g.forcing := by
  dsimp [forcing,bootstrapForcing]
  positivity

theorem prefix_bound {f : ℕ → ℝ} {n N : ℕ} {B : ℝ}
    (hn : n≤N) (hf : ∀j<N,0≤f j) (hB : (∑j∈range N,f j)≤B) :
    (∑j∈range n,f j)≤B := by
  apply le_trans _ hB
  exact sum_le_sum_of_subset_of_nonneg (range_mono hn) (fun j hj _ => hf j (mem_range.mp hj))

theorem budget_inside (g : FlowBootstrapGridData σ N T K I R ρ δ)
    {B SX SM : ℝ} (hB : 0≤B) (hI : 0≤I) (hR : 0≤R) (hρ : 0≤ρ) (hδ : 0≤δ)
    (hSX : (∑j∈range N,g.stateJump j)≤SX) (hSM : (∑j∈range N,g.matrixJump j)≤SM)
    {j : ℕ} (hj : j<N) {t : ℝ} (ht : t∈Icc (g.time j) (g.time (j+1))) :
    g.budget B j+g.forcing*(t-g.time j)≤(B+g.forcing*T+I*SX)*Real.exp (I*SM) := by
  apply bootstrapNodeBudget_inside_bound hB (g.forcing_nonneg hI hR hρ hδ) hI
    (fun i hi => g.duration_nonneg hi) g.stateJumpNonneg g.matrixJumpNonneg
    (by omega : j≤N) (sub_nonneg.mpr ht.1)
  · rw [g.duration_sum]
    linarith [ht.2,(g.timeMem (j+1) (by omega)).2]
  · exact prefix_bound (by omega : j≤N) g.stateJumpNonneg hSX
  · exact prefix_bound (by omega : j≤N) g.matrixJumpNonneg hSM

theorem nodeError_zero (g : FlowBootstrapGridData σ N T K I R ρ δ) (hσ : |σ|≤1) (a : State) :
    g.nodeError hσ a 0=‖a-g.reference 0 0‖ := by
  simp only [nodeError,bootstrapError,g.timeZero,supportFlow_zero,g.matrixInitial,Ring.inverse_one]
  rfl

end FlowBootstrapGridData
end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating bootstrap reference-grid audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating bootstrap reference-grid audit passed for {count} declarations."
