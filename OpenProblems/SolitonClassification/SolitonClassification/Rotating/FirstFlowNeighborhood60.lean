import SolitonClassification.Rotating.FirstTrueState60
import SolitonClassification.Rotating.LocalFlowNeighborhood

/-! A concrete nontrivial initial-data neighborhood of the candidate has
the proved short original flow, so actual first variations are available. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Candidate
set_option Elab.async false

def firstNeighborhoodRadius : ℚ := 1/10000

theorem initial_margin_checked :
    |rawInitial 0|+firstNeighborhoodRadius≤407/50 ∧
    |rawInitial 1|+firstNeighborhoodRadius≤33/8 ∧
    |rawInitial 2|+firstNeighborhoodRadius≤731/100 ∧
    |rawInitial 3|+firstNeighborhoodRadius≤731/100 ∧
    |rawInitial 4|+firstNeighborhoodRadius≤1/100 := by decide +kernel

theorem first_initial_margin : innerTubeMargin initial (firstNeighborhoodRadius:ℝ) := by
  rcases initial_margin_checked with ⟨h0,h1,h2,h3,h4⟩
  have lift (q r s : ℚ) (h : |q|+r≤s) : |(q:ℝ)|+(r:ℝ)≤(s:ℝ) := by
    rw [←Rat.cast_abs,←Rat.cast_add]
    exact Rat.cast_le.mpr h
  change |(rawInitial 0:ℝ)|+(firstNeighborhoodRadius:ℝ)≤407/50 ∧
    |(rawInitial 1:ℝ)|+(firstNeighborhoodRadius:ℝ)≤33/8 ∧
    |(rawInitial 2:ℝ)|+(firstNeighborhoodRadius:ℝ)≤731/100 ∧
    |(rawInitial 3:ℝ)|+(firstNeighborhoodRadius:ℝ)≤731/100 ∧
    |(rawInitial 4:ℝ)|+(firstNeighborhoodRadius:ℝ)≤1/100
  simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using
    And.intro (lift _ _ _ h0) (And.intro (lift _ _ _ h1)
      (And.intro (lift _ _ _ h2) (And.intro (lift _ _ _ h3) (lift _ _ _ h4))))

theorem first_flow_neighborhood (σ : ℝ) (hσ : |σ|≤1) {T : ℝ} (hT : T≤1/125) :
    FlowTubeNeighborhood σ hσ T initial (firstNeighborhoodRadius:ℝ) :=
  shortFlowTubeNeighborhood σ hσ first_initial_margin hT

theorem first_initial_mem_ball : initial∈Metric.ball initial (firstNeighborhoodRadius:ℝ) := by
  simp [firstNeighborhoodRadius]

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.first_flow_neighborhood
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Concrete first actual-flow neighborhood audit passed."
