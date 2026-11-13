module

public import SolitonClassification.Rotating.FlowMetricCoordinates

@[expose] public section

/-! Actual variational and inverse-variational growth on a reference
segment. The growth exponent is the proved moving-coordinate coefficient;
raw Jacobian growth across the full integration interval is not used. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem referenceInverse_continuousOn {M : ℝ → FlowEnd} {S : Set ℝ}
    (hM : ContinuousOn M S) (hu : ∀t∈S,IsUnit (M t)) :
    ContinuousOn (fun t => Ring.inverse (M t)) S := by
  intro t ht
  obtain ⟨u,hu⟩ := hu t ht
  have hc := NormedRing.inverse_continuousAt u
  rw [hu] at hc
  exact hc.comp_continuousWithinAt (f:=M) (hM t ht)

theorem matrix_left_growth {W C : ℝ → FlowEnd} {l r rate : ℝ}
    (hc : ContinuousOn W (Icc l r))
    (hd : ∀t∈Ico l r,HasDerivWithinAt W (C t*W t) (Ici t) t)
    (hC : ∀t∈Ico l r,‖C t‖≤rate) :
    ∀t∈Icc l r,‖W t‖≤‖W l‖*Real.exp (rate*(t-l)) := by
  have he := norm_le_gronwallBound_of_norm_deriv_right_le (ε:=0) hc hd (le_refl ‖W l‖)
    (fun t ht => by
      simpa only [add_zero] using (norm_mul_le (C t) (W t)).trans
        (mul_le_mul_of_nonneg_right (hC t ht) (norm_nonneg _)))
  simpa only [gronwallBound_ε0] using he

theorem matrix_right_growth {W C : ℝ → FlowEnd} {l r rate : ℝ}
    (hc : ContinuousOn W (Icc l r))
    (hd : ∀t∈Ico l r,HasDerivWithinAt W (-W t*C t) (Ici t) t)
    (hC : ∀t∈Ico l r,‖C t‖≤rate) :
    ∀t∈Icc l r,‖W t‖≤‖W l‖*Real.exp (rate*(t-l)) := by
  have he := norm_le_gronwallBound_of_norm_deriv_right_le (ε:=0) hc hd (le_refl ‖W l‖)
    (fun t ht => by
      rw [flowEnd_neg_mul,norm_neg,add_zero]
      exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left (hC t ht) (norm_nonneg _)).trans_eq (mul_comm _ _)))
  simpa only [gronwallBound_ε0] using he

theorem actual_metric_segment_growth (σ : ℝ) (hσ : |σ|≤1)
    {T l r rate : ℝ} {c a : State} {R : ℝ}
    (hreg : FlowTubeNeighborhood σ hσ T c R) (ha : a∈Metric.ball c R)
    (hl : 0≤l) (hr : r≤T) {M dM : ℝ → FlowEnd}
    (hM : ContinuousOn M (Icc l r)) (hu : ∀t∈Icc l r,IsUnit (M t))
    (hd : ∀t∈Ico l r,HasDerivWithinAt M (dM t) (Ici t) t)
    (hC : ∀t∈Ico l r,
      ‖flowMetricCoefficient (flowLinearCoefficient σ hσ a t) (M t) (dM t)‖≤rate) :
    ∀t∈Icc l r,
      (‖flowMetricForward σ hσ a M t‖≤
        ‖flowMetricForward σ hσ a M l‖*Real.exp (rate*(t-l))) ∧
      (‖flowMetricInverse σ hσ a M t‖≤
        ‖flowMetricInverse σ hσ a M l‖*Real.exp (rate*(t-l))) := by
  have hsub : Icc l r⊆Icc 0 T := Icc_subset_Icc hl hr
  have hPc := (supportFlow_fderiv_time_continuousOn σ hσ hreg ha).mono hsub
  have hQc := (supportFlow_inverse_continuousOn σ hσ hreg ha).mono hsub
  have hVc : ContinuousOn (flowMetricForward σ hσ a M) (Icc l r) :=
    (referenceInverse_continuousOn hM hu).mul hPc
  have hUc : ContinuousOn (flowMetricInverse σ hσ a M) (Icc l r) := hQc.mul hM
  have hV := matrix_left_growth hVc (fun t ht =>
    flowMetricForward_hasDerivWithinAt σ hσ hreg ha ⟨hl.trans ht.1,ht.2.trans_le hr⟩
      (hd t ht) (hu t (Ico_subset_Icc_self ht))) hC
  have hU := matrix_right_growth hUc (fun t ht =>
    flowMetricInverse_hasDerivWithinAt σ hσ hreg ha ⟨hl.trans ht.1,ht.2.trans_le hr⟩
      (hd t ht) (hu t (Ico_subset_Icc_self ht))) hC
  exact fun t ht => ⟨hV t ht,hU t ht⟩

theorem actual_matrix_segment_bounds (σ : ℝ) (hσ : |σ|≤1)
    {T l r rate K I : ℝ} {c a : State} {R : ℝ}
    (hK : 0≤K)
    (hreg : FlowTubeNeighborhood σ hσ T c R) (ha : a∈Metric.ball c R)
    (hl : 0≤l) (hr : r≤T) {M dM : ℝ → FlowEnd}
    (hM : ContinuousOn M (Icc l r)) (hu : ∀t∈Icc l r,IsUnit (M t))
    (hd : ∀t∈Ico l r,HasDerivWithinAt M (dM t) (Ici t) t)
    (hC : ∀t∈Ico l r,
      ‖flowMetricCoefficient (flowLinearCoefficient σ hσ a t) (M t) (dM t)‖≤rate)
    (hMb : ∀t∈Icc l r,‖M t‖≤K) (hIb : ∀t∈Icc l r,‖Ring.inverse (M t)‖≤I) :
    ∀t∈Icc l r,
      (‖fderiv ℝ (supportFlow σ hσ t) a‖≤
        K*(‖flowMetricForward σ hσ a M l‖*Real.exp (rate*(t-l)))) ∧
      (‖supportFlowInverse σ hσ a t‖≤
        (‖flowMetricInverse σ hσ a M l‖*Real.exp (rate*(t-l)))*I) := by
  intro t ht
  have hh := actual_metric_segment_growth σ hσ hreg ha hl hr hM hu hd hC t ht
  constructor
  · rw [actual_fderiv_from_metric σ hσ a M t (hu t ht)]
    exact (norm_mul_le _ _).trans (mul_le_mul (hMb t ht) hh.1 (norm_nonneg _) hK)
  · rw [actual_inverse_from_metric σ hσ a M t (hu t ht)]
    exact (norm_mul_le _ _).trans (mul_le_mul hh.2 (hIb t ht) (norm_nonneg _) (by positivity))

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating actual moving-matrix segment audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating actual moving-matrix segment audit passed for {count} declarations."

end
