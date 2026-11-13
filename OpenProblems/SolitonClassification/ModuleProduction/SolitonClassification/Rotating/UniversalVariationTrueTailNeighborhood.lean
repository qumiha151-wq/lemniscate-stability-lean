module

public import SolitonClassification.Rotating.FlowTube
public import SolitonClassification.Rotating.FlowDifferentiability

@[expose] public section

/-! A genuine original-field neighborhood even at the innerTube boundary.
The small initial ball need not stay in innerTube. Global clipped-flow
coordinate displacement bounds put the entire ball's trajectories in the
outerTube for times at most1/125. No orbit enclosure is assumed. -/
namespace SolitonClassification.Rotating.UniversalMajorant
noncomputable section
open Set Metric
set_option maxHeartbeats 3000000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

theorem innerTube_flowTubeNeighborhood (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) {T : ℝ} (hT : T≤1/125) :
    FlowTubeNeighborhood σ hσ T a (1/10000) := by
  intro y hy t ht
  have hn : ‖y-a‖≤(1:ℝ)/10000 := by
    simpa only [dist_eq_norm] using (mem_ball.mp hy).le
  have htmax : t≤1/125 := ht.2.trans hT
  have hb (i : Fin 6) : |supportFlow σ hσ t y i|≤coordinateSpeed i*t+1/10000+|a i| := by
    have hd := supportFlow_coordinate_displacement σ hσ y t i
    rw [abs_of_nonneg ht.1] at hd
    have hi : |y i-a i|≤(1:ℝ)/10000 := (coordinate_bound (y-a) i).trans hn
    calc
      _ = |(supportFlow σ hσ t y i-y i)+(y i-a i)+a i| := by ring_nf
      _ ≤ |(supportFlow σ hσ t y i-y i)+(y i-a i)|+|a i| := abs_add_le _ _
      _ ≤ (|supportFlow σ hσ t y i-y i|+|y i-a i|)+|a i| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ _ := by linarith
  rcases ha with ⟨a0,a1,a2,a3,a4⟩
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  have h4 := hb 4
  norm_num [coordinateSpeed] at h0 h1 h2 h3 h4
  change |supportFlow σ hσ t y 2|≤75*t+1/10000+|a 2| at h2
  change |supportFlow σ hσ t y 3|≤75*t+1/10000+|a 3| at h3
  change |supportFlow σ hσ t y 4|≤0*t+1/10000+|a 4| at h4
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

/-- Differentiability itself is also a conclusion at every inner-box point. -/
theorem innerTube_supportFlow_hasFDerivAt (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) {t : ℝ} (ht : t∈Icc 0 ((1:ℝ)/125)) :
    HasFDerivAt (supportFlow σ hσ t) (fderiv ℝ (supportFlow σ hσ t) a) a :=
  supportFlow_hasFDerivAt_initial σ hσ (innerTube_flowTubeNeighborhood σ hσ ha le_rfl)
    (Metric.mem_ball_self (by norm_num)) ht

end
end SolitonClassification.Rotating.UniversalMajorant

#print axioms SolitonClassification.Rotating.UniversalMajorant.innerTube_flowTubeNeighborhood
open Lean Elab Command in
run_cmd do
  for (name, _) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
  logInfo "Boundary-safe actual flow neighborhood audit passed; standard axioms only."

end
