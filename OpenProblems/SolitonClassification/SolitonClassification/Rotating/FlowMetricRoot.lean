import SolitonClassification.Rotating.FlowMetricGlobal
import SolitonClassification.Rotating.FlowInverseRoot

/-! Uniform finite-grid bounds fill the actual-root certificate's P/Q
fields. No actual P/Q norm estimate is assumed in this conversion. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Finset
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem actualFlowMatrixBounds_of_reference_grids (σ : ℝ) (hσ : |σ|≤1)
    {N : ℕ} {T K I E ρ B J : ℝ} {c : State} {R : ℝ} {S : Set State}
    (hreg : FlowTubeNeighborhood σ hσ T c R) (hsub : S⊆Metric.ball c R)
    (hN : 0<N) (hK : 0≤K) (hI : 0≤I) (hE : 0≤E) (hρ : 0≤ρ)
    (grid : ∀a∈S,FlowMetricGridData σ hσ a N T K I E ρ)
    (hjump : ∀a (ha : a∈S),(∑j∈range N,(grid a ha).jump j)≤J)
    (hbudget : Real.exp (I*(4*E*K+ρ)*T+I*J)≤B) :
    ActualFlowMatrixBounds σ hσ T c R S (K*B) (I*B) := by
  refine ⟨hreg,?_,?_⟩
  · intro a ha t ht
    exact ((grid a ha).actual_matrix_bounds_of_budget hreg (hsub ha) hN hK hI hE hρ
      (hjump a ha) hbudget t ht).1
  · intro a ha t ht
    exact ((grid a ha).actual_matrix_bounds_of_budget hreg (hsub ha) hN hK hI hE hρ
      (hjump a ha) hbudget t ht).2

/-- The intended actual 8000/16000 bounds follow from reference
2000/4000 bounds and a proved exponential budget at most four. This
theorem still requires the true grid and state-error certificates. -/
theorem actualFlowMatrixBounds_8000_16000_of_reference_grids (σ : ℝ) (hσ : |σ|≤1)
    {N : ℕ} {T E ρ J : ℝ} {c : State} {R : ℝ} {S : Set State}
    (hreg : FlowTubeNeighborhood σ hσ T c R) (hsub : S⊆Metric.ball c R)
    (hN : 0<N) (hE : 0≤E) (hρ : 0≤ρ)
    (grid : ∀a∈S,FlowMetricGridData σ hσ a N T 2000 4000 E ρ)
    (hjump : ∀a (ha : a∈S),(∑j∈range N,(grid a ha).jump j)≤J)
    (hbudget : Real.exp (4000*(4*E*2000+ρ)*T+4000*J)≤4) :
    ActualFlowMatrixBounds σ hσ T c R S 8000 16000 := by
  convert! actualFlowMatrixBounds_of_reference_grids σ hσ hreg hsub hN
    (by norm_num : 0≤(2000:ℝ)) (by norm_num : 0≤(4000:ℝ)) hE hρ grid hjump hbudget using 1 <;> norm_num

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating finite-grid actual-root bridge audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating finite-grid actual-root bridge audit passed for {count} declarations."
