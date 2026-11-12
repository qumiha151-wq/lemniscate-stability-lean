import SolitonClassification.Rotating.FlowTube
import SolitonClassification.Rotating.FlowDifferentiability

/-! A checkable coordinate margin supplies a genuine whole-neighborhood
original-flow tube for the differentiability and variational theorems. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Metric
set_option Elab.async false

def innerTubeMargin (a : State) (r : ℝ) : Prop :=
  |a 0|+r≤407/50 ∧ |a 1|+r≤33/8 ∧ |a 2|+r≤731/100 ∧
  |a 3|+r≤731/100 ∧ |a 4|+r≤1/100

theorem ball_mem_innerTube {a y : State} {r : ℝ} (h : innerTubeMargin a r)
    (hy : y∈ball a r) : y∈innerTube := by
  have hn : ‖y-a‖≤r := by simpa only [dist_eq_norm] using (mem_ball.mp hy).le
  have hb (i : Fin 6) : |y i|≤|a i|+r := by
    have hi : |y i-a i|≤r := (coordinate_bound (y-a) i).trans hn
    calc
      _ ≤ |y i-a i|+|a i| := by simpa using abs_add_le (y i-a i) (a i)
      _ ≤ _ := by linarith
  exact ⟨(hb 0).trans h.1,(hb 1).trans h.2.1,(hb 2).trans h.2.2.1,
    (hb 3).trans h.2.2.2.1,(hb 4).trans h.2.2.2.2⟩

theorem shortFlowTubeNeighborhood (σ : ℝ) (hσ : |σ|≤1)
    {a : State} {r T : ℝ} (ha : innerTubeMargin a r) (hT : T≤1/125) :
    FlowTubeNeighborhood σ hσ T a r := by
  intro y hy t ht
  exact supportFlow_short_mem_outerTube σ hσ (ball_mem_innerTube ha hy) ht.1 (ht.2.trans hT)

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.shortFlowTubeNeighborhood
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Actual local flow neighborhood from coordinate margin audit passed."
