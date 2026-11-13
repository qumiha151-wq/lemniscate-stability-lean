module

public import SolitonClassification.Rotating.FlowVariational

@[expose] public section

/-! The actual initial derivative satisfies the actual linear variational
ODE up to the initial endpoint in the right-derivative sense. This boundary
form is sufficient for closed-interval ODE uniqueness and Duhamel estimates. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

theorem supportFlow_fderiv_hasDerivWithinAt (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} {c : State} {R : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R)
    {a : State} (ha : a∈Metric.ball c R) {t : ℝ} (ht : t∈Ico 0 T) :
    HasDerivWithinAt (fun s => fderiv ℝ (supportFlow σ hσ s) a)
      ((flowLinearCoefficient σ hσ a t).comp (fderiv ℝ (supportFlow σ hσ t) a)) (Ici t) t := by
  have hc := flowVariationalIntegrand_continuousOn σ hσ hreg ha
  have hn : Icc (0:ℝ) T∈𝓝[Ici t] t :=
    Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (fun _ hs => ⟨ht.1.trans hs.1,hs.2⟩)
  have hint : IntervalIntegrable (flowVariationalIntegrand σ hσ a) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    apply hc.mono
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc_right ht.2.le
  have hn' : Icc (0:ℝ) T∈𝓝[Ioi t] t :=
    nhdsWithin_mono t Ioi_subset_Ici_self hn
  have hmeas : StronglyMeasurableAtFilter (flowVariationalIntegrand σ hσ a) (𝓝[Ioi t] t) volume :=
    ⟨Icc 0 T,hn',hc.aestronglyMeasurable measurableSet_Icc⟩
  have hi := intervalIntegral.integral_hasDerivWithinAt_right (s:=Ici t) (t:=Ioi t)
    hint hmeas ((hc t ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin hn')
  have he : (fun s => fderiv ℝ (supportFlow σ hσ s) a)=ᶠ[𝓝[Ici t] t]
      fun s => ContinuousLinearMap.id ℝ State+∫u in (0:ℝ)..s,flowVariationalIntegrand σ hσ a u := by
    filter_upwards [hn] with s hs
    exact supportFlow_fderiv_integral σ hσ hreg ha hs
  exact (hi.const_add (ContinuousLinearMap.id ℝ State)).congr_of_eventuallyEq_of_mem he (le_refl t)

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating first-variation ODE audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating first-variation ODE audit passed for {count} declarations."

end
