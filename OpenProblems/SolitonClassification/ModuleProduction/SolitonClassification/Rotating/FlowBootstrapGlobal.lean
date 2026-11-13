module

public import SolitonClassification.Rotating.FlowBootstrapGridData

@[expose] public section

/-! Finite induction applies the first-threshold argument before each
reset. Actual tube membership and physical state error are conclusions.
The global clipped flow supplies existence without any bootstrap premise. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Finset
set_option backward.isDefEq.respectTransparency false

namespace FlowBootstrapGridData
variable {σ : ℝ} {N : ℕ} {T K I R ρ δ : ℝ}

theorem segment_of_node_bound (g : FlowBootstrapGridData σ N T K I R ρ δ)
    (hσ : |σ|≤1) (a : State) {B SX SM : ℝ}
    (hB : 0≤B) (hK : 0≤K) (hI : 0≤I) (hR : 0≤R) (hρ : 0≤ρ) (hδ : 0≤δ)
    (hSX : (∑j∈range N,g.stateJump j)≤SX) (hSM : (∑j∈range N,g.matrixJump j)≤SM)
    (hstrict : (B+g.forcing*T+I*SX)*Real.exp (I*SM)<R)
    {j : ℕ} (hj : j<N) (hnode : g.nodeError hσ a j≤g.budget B j) :
    ∀t∈Icc (g.time j) (g.time (j+1)),
      supportFlow σ hσ t a∈outerTube ∧
      ‖bootstrapError σ hσ a (g.reference j) (g.matrix j) t‖<R ∧
      ‖bootstrapError σ hσ a (g.reference j) (g.matrix j) t‖≤
        g.nodeError hσ a j+g.forcing*(t-g.time j) ∧
      ‖supportFlow σ hσ t a-g.reference j t‖≤K*R := by
  have hend : g.time (j+1)∈Icc (g.time j) (g.time (j+1)) := ⟨g.timeStep j hj,le_rfl⟩
  have hb := g.budget_inside hB hI hR hρ hδ hSX hSM hj hend
  have hs : g.nodeError hσ a j+g.forcing*(g.time (j+1)-g.time j)<R := by linarith
  exact bootstrap_reference_segment σ hσ a hK hI hR hρ hδ
    (g.referenceContinuous j hj) (g.matrixContinuous j hj) (g.matrixUnit j hj)
    (g.referenceDerivative j hj) (g.matrixDerivative j hj) (g.matrixBound j hj)
    (g.inverseBound j hj) (g.matrixResidualBound j hj) (g.stateResidualBound j hj)
    (g.referenceMargin j hj) hs

theorem node_bound (g : FlowBootstrapGridData σ N T K I R ρ δ)
    (hσ : |σ|≤1) (a : State) {B SX SM : ℝ}
    (hB : 0≤B) (hK : 0≤K) (hI : 0≤I) (hR : 0≤R) (hρ : 0≤ρ) (hδ : 0≤δ)
    (hSX : (∑j∈range N,g.stateJump j)≤SX) (hSM : (∑j∈range N,g.matrixJump j)≤SM)
    (hstrict : (B+g.forcing*T+I*SX)*Real.exp (I*SM)<R)
    (hinit : ‖a-g.reference 0 0‖≤B) :
    ∀n≤N,g.nodeError hσ a n≤g.budget B n := by
  intro n hn
  induction n with
  | zero => simpa only [g.nodeError_zero,budget,bootstrapNodeBudget] using hinit
  | succ n ih =>
    have hn' : n<N := by omega
    have hprev := ih (by omega)
    have hend : g.time (n+1)∈Icc (g.time n) (g.time (n+1)) := ⟨g.timeStep n hn',le_rfl⟩
    have hs := g.segment_of_node_bound hσ a hB hK hI hR hρ hδ hSX hSM hstrict hn' hprev _ hend
    have hr := bootstrap_reset_bound (x:=supportFlow σ hσ (g.time (n+1)) a)
      (g.matrixUnit n hn' _ hend) (g.nodeUnit (n+1) (by omega)) hI
      (g.nodeInverseBound (n+1) (by omega)) (g.matrixReset n hn') (g.stateReset n hn')
    change g.nodeError hσ a (n+1)≤(1+I*g.matrixJump n)*
      ‖bootstrapError σ hσ a (g.reference n) (g.matrix n) (g.time (n+1))‖+I*g.stateJump n at hr
    have hjn := g.matrixJumpNonneg n hn'
    have hfactor : 0≤1+I*g.matrixJump n := by positivity
    have he : ‖bootstrapError σ hσ a (g.reference n) (g.matrix n) (g.time (n+1))‖≤
        g.budget B n+g.forcing*g.duration n := by
      dsimp [duration]
      linarith [hs.2.2.1]
    exact hr.trans (by
      change (1+I*g.matrixJump n)*_+I*g.stateJump n≤
        (1+I*g.matrixJump n)*(g.budget B n+g.forcing*g.duration n)+I*g.stateJump n
      linarith [mul_le_mul_of_nonneg_left he hfactor])

theorem actual_on_segment (g : FlowBootstrapGridData σ N T K I R ρ δ)
    (hσ : |σ|≤1) (a : State) {B SX SM : ℝ}
    (hB : 0≤B) (hK : 0≤K) (hI : 0≤I) (hR : 0≤R) (hρ : 0≤ρ) (hδ : 0≤δ)
    (hSX : (∑j∈range N,g.stateJump j)≤SX) (hSM : (∑j∈range N,g.matrixJump j)≤SM)
    (hstrict : (B+g.forcing*T+I*SX)*Real.exp (I*SM)<R)
    (hinit : ‖a-g.reference 0 0‖≤B) {j : ℕ} (hj : j<N) :
    ∀t∈Icc (g.time j) (g.time (j+1)),
      supportFlow σ hσ t a∈outerTube ∧ ‖supportFlow σ hσ t a-g.reference j t‖≤K*R := by
  have hn := g.node_bound hσ a hB hK hI hR hρ hδ hSX hSM hstrict hinit j (by omega)
  intro t ht
  have hs := g.segment_of_node_bound hσ a hB hK hI hR hρ hδ hSX hSM hstrict hj hn t ht
  exact ⟨hs.1,hs.2.2.2⟩

theorem actual_mem_outerTube (g : FlowBootstrapGridData σ N T K I R ρ δ)
    (hσ : |σ|≤1) (a : State) {B SX SM : ℝ}
    (hN : 0<N) (hB : 0≤B) (hK : 0≤K) (hI : 0≤I) (hR : 0≤R) (hρ : 0≤ρ) (hδ : 0≤δ)
    (hSX : (∑j∈range N,g.stateJump j)≤SX) (hSM : (∑j∈range N,g.matrixJump j)≤SM)
    (hstrict : (B+g.forcing*T+I*SX)*Real.exp (I*SM)<R)
    (hinit : ‖a-g.reference 0 0‖≤B) :
    ∀t∈Icc 0 T,supportFlow σ hσ t a∈outerTube := by
  intro t ht
  have ht' : t∈Icc (g.time 0) (g.time N) := by simpa only [g.timeZero,g.timeLast] using ht
  obtain ⟨j,hj,hjt⟩ := metric_grid_cover g.time hN g.timeStep ht'
  exact (g.actual_on_segment hσ a hB hK hI hR hρ hδ hSX hSM hstrict hinit hj t hjt).1

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
          throwError "Rotating global actual state-bootstrap audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating global actual state-bootstrap audit passed for {count} declarations."

end
