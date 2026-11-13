module

public import SolitonClassification.Rotating.FlowMetricDeviationGlobal
public import SolitonClassification.Rotating.FlowBootstrapMatrices

@[expose] public section

/-! Uniform actual variational deviation after the proved nonlinear
state/tube bootstrap. The numerical budget δrel is free; no Taylor order,
matrix accuracy threshold, or whole-grid certificate is presumed. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Finset
set_option backward.isDefEq.respectTransparency false

namespace FlowBootstrapGridData
variable {σ : ℝ} {N : ℕ} {T K I R ρ δ : ℝ}

theorem actualDeviation (g : FlowBootstrapGridData σ N T K I R ρ δ)
    (hσ : |σ|≤1) {B SX SM δrel : ℝ} {c : State} {r : ℝ}
    (hN : 0<N) (hB : 0≤B) (hK : 0≤K) (hI : 0≤I) (hR : 0≤R) (hρ : 0≤ρ) (hδ : 0≤δ)
    (hSX : (∑j∈range N,g.stateJump j)≤SX) (hSM : (∑j∈range N,g.matrixJump j)≤SM)
    (hstrict : (B+g.forcing*T+I*SX)*Real.exp (I*SM)<R)
    (hcenter : ‖c-g.reference 0 0‖+r≤B)
    (hmatrixBudget : Real.exp (I*(4*(K*R)*K+ρ)*T+I*SM)≤1+δrel) :
    ∀a∈Metric.ball c r,∀j<N,∀t∈Icc (g.time j) (g.time (j+1)),
      ‖fderiv ℝ (supportFlow σ hσ t) a-g.matrix j t‖≤K*δrel := by
  intro a ha j hj t ht
  let grid := g.toMetricGrid hσ a hB hK hI hR hρ hδ hSX hSM hstrict (g.initial_error_of_ball hcenter ha)
  have hreg := g.tubeNeighborhood hσ hN hB hK hI hR hρ hδ hSX hSM hstrict hcenter
  exact grid.actual_deviation_on_segment_of_budget hreg ha hK hI (mul_nonneg hK hR) hρ
    hSM hmatrixBudget hj ht

/-- The terminal reset matrix has norm at most K plus its last reset
defect, derived from the grid. This formula makes that final reset
explicit rather than silently using the last segment's reference. -/
theorem actualDeviation_terminal (g : FlowBootstrapGridData σ N T K I R ρ δ)
    (hσ : |σ|≤1) {B SX SM δrel : ℝ} {c : State} {r : ℝ}
    (hN : 0<N) (hB : 0≤B) (hK : 0≤K) (hI : 0≤I) (hR : 0≤R) (hρ : 0≤ρ) (hδ : 0≤δ)
    (hSX : (∑j∈range N,g.stateJump j)≤SX) (hSM : (∑j∈range N,g.matrixJump j)≤SM)
    (hstrict : (B+g.forcing*T+I*SX)*Real.exp (I*SM)<R)
    (hcenter : ‖c-g.reference 0 0‖+r≤B)
    (hmatrixBudget : Real.exp (I*(4*(K*R)*K+ρ)*T+I*SM)≤1+δrel) :
    ∀a∈Metric.ball c r,‖fderiv ℝ (supportFlow σ hσ T) a-g.matrix N T‖≤
      (K+g.matrixJump (N-1))*δrel := by
  intro a ha
  let grid := g.toMetricGrid hσ a hB hK hI hR hρ hδ hSX hSM hstrict (g.initial_error_of_ball hcenter ha)
  have hreg := g.tubeNeighborhood hσ hN hB hK hI hR hρ hδ hSX hSM hstrict hcenter
  have hh := grid.actual_deviation_at_node_of_budget hreg ha hK hI (mul_nonneg hK hR) hρ
    hSM hmatrixBudget (le_refl N) (grid.matrix_node_bound_from_reset hN (le_refl N))
  change ‖fderiv ℝ (supportFlow σ hσ (g.time N)) a-g.matrix N (g.time N)‖≤
    (K+g.matrixJump (N-1))*δrel at hh
  simpa only [g.timeLast] using hh

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
          throwError "Rotating bootstrapped actual matrix-deviation audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating bootstrapped actual matrix-deviation audit passed for {count} declarations."
