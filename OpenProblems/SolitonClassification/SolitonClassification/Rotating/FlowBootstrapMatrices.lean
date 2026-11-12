import SolitonClassification.Rotating.FlowBootstrapNeighborhood
import SolitonClassification.Rotating.FlowMetricRoot

/-! The state/tube bootstrap discharges the previous global matrix
comparison's actual tube and state-error premises. Inputs now concern
real reference data, local residuals, reset defects and strict budgets;
there is no assumed bound for actual state error, actual P or actual Q. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Finset
set_option backward.isDefEq.respectTransparency false

namespace FlowBootstrapGridData
variable {σ : ℝ} {N : ℕ} {T K I R ρ δ : ℝ}

def toMetricGrid (g : FlowBootstrapGridData σ N T K I R ρ δ)
    (hσ : |σ|≤1) (a : State) {B SX SM : ℝ}
    (hB : 0≤B) (hK : 0≤K) (hI : 0≤I) (hR : 0≤R) (hρ : 0≤ρ) (hδ : 0≤δ)
    (hSX : (∑j∈range N,g.stateJump j)≤SX) (hSM : (∑j∈range N,g.matrixJump j)≤SM)
    (hstrict : (B+g.forcing*T+I*SX)*Real.exp (I*SM)<R)
    (hinit : ‖a-g.reference 0 0‖≤B) : FlowMetricGridData σ hσ a N T K I (K*R) ρ where
  time := g.time
  matrix := g.matrix
  reference := g.reference
  residual := g.matrixResidual
  jump := g.matrixJump
  timeZero := g.timeZero
  timeLast := g.timeLast
  timeMem := g.timeMem
  timeStep := g.timeStep
  matrixInitial := g.matrixInitial
  nodeUnit := g.nodeUnit
  nodeInverseBound := g.nodeInverseBound
  matrixContinuous := g.matrixContinuous
  matrixUnit := g.matrixUnit
  matrixDerivative := g.matrixDerivative
  matrixBound := g.matrixBound
  inverseBound := g.inverseBound
  referenceTube := fun j hj t ht => outerTube_of_margin (g.referenceMargin j hj t ht)
    (by simpa using mul_nonneg hK hR)
  stateError := fun j hj t ht =>
    (g.actual_on_segment hσ a hB hK hI hR hρ hδ hSX hSM hstrict hinit hj t ht).2
  residualBound := g.matrixResidualBound
  jumpNonneg := g.matrixJumpNonneg
  resetBound := g.matrixReset

theorem actualMatrixBounds (g : FlowBootstrapGridData σ N T K I R ρ δ)
    (hσ : |σ|≤1) {B SX SM D : ℝ} {c : State} {r : ℝ} {S : Set State}
    (hN : 0<N) (hB : 0≤B) (hK : 0≤K) (hI : 0≤I) (hR : 0≤R) (hρ : 0≤ρ) (hδ : 0≤δ)
    (hSX : (∑j∈range N,g.stateJump j)≤SX) (hSM : (∑j∈range N,g.matrixJump j)≤SM)
    (hstrict : (B+g.forcing*T+I*SX)*Real.exp (I*SM)<R)
    (hcenter : ‖c-g.reference 0 0‖+r≤B) (hsub : S⊆Metric.ball c r)
    (hmatrixBudget : Real.exp (I*(4*(K*R)*K+ρ)*T+I*SM)≤D) :
    ActualFlowMatrixBounds σ hσ T c r S (K*D) (I*D) := by
  let grid := fun a (ha : a∈S) => g.toMetricGrid hσ a hB hK hI hR hρ hδ hSX hSM hstrict
    (g.initial_error_of_ball hcenter (hsub ha))
  have hreg := g.tubeNeighborhood hσ hN hB hK hI hR hρ hδ hSX hSM hstrict hcenter
  exact actualFlowMatrixBounds_of_reference_grids σ hσ hreg hsub hN hK hI
    (mul_nonneg hK hR) hρ grid (fun _ _ => hSM) hmatrixBudget

/-- A specialized bridge to the intended 8000/16000 shooting bounds.
This is conditional on the real reference-grid certificate, including
its strict state budget. No 8000-segment numerical data is asserted here. -/
theorem actualMatrixBounds_8000_16000
    (g : FlowBootstrapGridData σ N T 2000 4000 R ρ δ)
    (hσ : |σ|≤1) {B SX SM : ℝ} {c : State} {r : ℝ} {S : Set State}
    (hN : 0<N) (hB : 0≤B) (hR : 0≤R) (hρ : 0≤ρ) (hδ : 0≤δ)
    (hSX : (∑j∈range N,g.stateJump j)≤SX) (hSM : (∑j∈range N,g.matrixJump j)≤SM)
    (hstrict : (B+g.forcing*T+4000*SX)*Real.exp (4000*SM)<R)
    (hcenter : ‖c-g.reference 0 0‖+r≤B) (hsub : S⊆Metric.ball c r)
    (hmatrixBudget : Real.exp (4000*(4*(2000*R)*2000+ρ)*T+4000*SM)≤4) :
    ActualFlowMatrixBounds σ hσ T c r S 8000 16000 := by
  convert! g.actualMatrixBounds hσ hN hB (by norm_num : 0≤(2000:ℝ))
    (by norm_num : 0≤(4000:ℝ)) hR hρ hδ hSX hSM hstrict hcenter hsub hmatrixBudget using 1 <;> norm_num

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
          throwError "Rotating actual state-to-matrix bootstrap audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating actual state-to-matrix bootstrap audit passed for {count} declarations."
