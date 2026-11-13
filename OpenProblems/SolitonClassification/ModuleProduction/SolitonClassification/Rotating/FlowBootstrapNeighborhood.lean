module

public import SolitonClassification.Rotating.FlowBootstrapGlobal

@[expose] public section

/-! Uniform confinement on an actual open initial-state ball. This
supplies the neighborhood needed for differentiating the original ODE;
membership of the actual flow in the tube is never assumed. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Finset
set_option backward.isDefEq.respectTransparency false

namespace FlowBootstrapGridData
variable {σ : ℝ} {N : ℕ} {T K I R ρ δ : ℝ}

theorem initial_error_of_ball (g : FlowBootstrapGridData σ N T K I R ρ δ)
    {c a : State} {r B : ℝ} (hcenter : ‖c-g.reference 0 0‖+r≤B)
    (ha : a∈Metric.ball c r) : ‖a-g.reference 0 0‖≤B := by
  have ha' : ‖a-c‖<r := by simpa only [Metric.mem_ball,dist_eq_norm] using ha
  have htri : ‖a-g.reference 0 0‖≤‖a-c‖+‖c-g.reference 0 0‖ := by
    calc
      _ = ‖(a-c)+(c-g.reference 0 0)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  linarith

theorem tubeNeighborhood (g : FlowBootstrapGridData σ N T K I R ρ δ)
    (hσ : |σ|≤1) {B SX SM : ℝ} {c : State} {r : ℝ}
    (hN : 0<N) (hB : 0≤B) (hK : 0≤K) (hI : 0≤I) (hR : 0≤R) (hρ : 0≤ρ) (hδ : 0≤δ)
    (hSX : (∑j∈range N,g.stateJump j)≤SX) (hSM : (∑j∈range N,g.matrixJump j)≤SM)
    (hstrict : (B+g.forcing*T+I*SX)*Real.exp (I*SM)<R)
    (hcenter : ‖c-g.reference 0 0‖+r≤B) : FlowTubeNeighborhood σ hσ T c r := by
  intro a ha
  exact g.actual_mem_outerTube hσ a hN hB hK hI hR hρ hδ hSX hSM hstrict
    (g.initial_error_of_ball hcenter ha)

/-- Actual original-field ODE on the entire covered time interval, for
every point of the initial-state ball. The grid endpoint is the exact
time horizon; a larger scalar budget does not extend this conclusion. -/
theorem original_derivative_of_bootstrap (g : FlowBootstrapGridData σ N T K I R ρ δ)
    (hσ : |σ|≤1) {B SX SM : ℝ} {c a : State} {r t : ℝ}
    (hN : 0<N) (hB : 0≤B) (hK : 0≤K) (hI : 0≤I) (hR : 0≤R) (hρ : 0≤ρ) (hδ : 0≤δ)
    (hSX : (∑j∈range N,g.stateJump j)≤SX) (hSM : (∑j∈range N,g.matrixJump j)≤SM)
    (hstrict : (B+g.forcing*T+I*SX)*Real.exp (I*SM)<R)
    (hcenter : ‖c-g.reference 0 0‖+r≤B) (ha : a∈Metric.ball c r) (ht : t∈Icc 0 T) :
    HasDerivAt (fun s => supportFlow σ hσ s a) (σ • field (supportFlow σ hσ t a)) t :=
  supportFlow_original_derivative σ hσ a t
    (g.tubeNeighborhood hσ hN hB hK hI hR hρ hδ hSX hSM hstrict hcenter a ha t ht)

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
          throwError "Rotating actual initial-ball bootstrap audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating actual initial-ball bootstrap audit passed for {count} declarations."

end
