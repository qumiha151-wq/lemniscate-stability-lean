import SolitonClassification.Rotating.FlowMetricSegment

/-! Actual moving-matrix deviation from identity on a segment. This
retains the additive forcing from W'=C*W after subtracting Id. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

theorem gronwallBound_same_rate (d rate t : ℝ) :
    gronwallBound d rate rate t+1=(d+1)*Real.exp (rate*t) := by
  by_cases hr : rate=0
  · subst rate
    simp only [gronwallBound_K0,zero_mul,Real.exp_zero,mul_one,add_zero]
  · rw [gronwallBound_of_K_ne_0 hr]
    dsimp
    rw [div_self hr]
    ring

theorem matrix_left_deviation_growth {W C : ℝ → FlowEnd} {l r rate : ℝ}
    (hrate : 0≤rate) (hc : ContinuousOn W (Icc l r))
    (hd : ∀t∈Ico l r,HasDerivWithinAt W (C t*W t) (Ici t) t)
    (hC : ∀t∈Ico l r,‖C t‖≤rate) :
    ∀t∈Icc l r,‖W t-1‖+1≤(‖W l-1‖+1)*Real.exp (rate*(t-l)) := by
  have hW (t : ℝ) : ‖W t‖≤‖W t-1‖+1 := by
    have h := norm_add_le (W t-1) (1:FlowEnd)
    simpa only [sub_add_cancel,norm_one] using h
  have hbound : ∀t∈Ico l r,‖C t*W t‖≤rate*‖W t-1‖+rate := by
    intro t ht
    have h := (norm_mul_le (C t) (W t)).trans
      (mul_le_mul (hC t ht) (hW t) (norm_nonneg _) hrate)
    nlinarith
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (K:=rate) (ε:=rate)
    (hc.sub continuousOn_const) (fun t ht => (hd t ht).sub_const (1:FlowEnd))
    (le_refl ‖W l-1‖) hbound
  intro t ht
  have h := hg t ht
  change ‖W t-1‖≤gronwallBound ‖W l-1‖ rate rate (t-l) at h
  have he := gronwallBound_same_rate ‖W l-1‖ rate (t-l)
  linarith

theorem actual_metric_segment_deviation (σ : ℝ) (hσ : |σ|≤1)
    {T l r rate : ℝ} {c a : State} {R : ℝ}
    (hrate : 0≤rate) (hreg : FlowTubeNeighborhood σ hσ T c R) (ha : a∈Metric.ball c R)
    (hl : 0≤l) (hr : r≤T) {M dM : ℝ → FlowEnd}
    (hM : ContinuousOn M (Icc l r)) (hu : ∀t∈Icc l r,IsUnit (M t))
    (hd : ∀t∈Ico l r,HasDerivWithinAt M (dM t) (Ici t) t)
    (hC : ∀t∈Ico l r,
      ‖flowMetricCoefficient (flowLinearCoefficient σ hσ a t) (M t) (dM t)‖≤rate) :
    ∀t∈Icc l r,‖flowMetricForward σ hσ a M t-1‖+1≤
      (‖flowMetricForward σ hσ a M l-1‖+1)*Real.exp (rate*(t-l)) := by
  have hsub : Icc l r⊆Icc 0 T := Icc_subset_Icc hl hr
  have hPc := (supportFlow_fderiv_time_continuousOn σ hσ hreg ha).mono hsub
  have hVc : ContinuousOn (flowMetricForward σ hσ a M) (Icc l r) :=
    (referenceInverse_continuousOn hM hu).mul hPc
  exact matrix_left_deviation_growth hrate hVc (fun t ht =>
    flowMetricForward_hasDerivWithinAt σ hσ hreg ha ⟨hl.trans ht.1,ht.2.trans_le hr⟩
      (hd t ht) (hu t (Ico_subset_Icc_self ht))) hC

theorem actual_fderiv_deviation_from_metric (σ : ℝ) (hσ : |σ|≤1) (a : State)
    (M : ℝ → FlowEnd) (t : ℝ) (hu : IsUnit (M t)) :
    fderiv ℝ (supportFlow σ hσ t) a-M t=M t*(flowMetricForward σ hσ a M t-1) := by
  rw [actual_fderiv_from_metric σ hσ a M t hu,mul_sub,mul_one]

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating actual matrix segment-deviation audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating actual matrix segment-deviation audit passed for {count} declarations."
