import CentroidEscape.MetricBootstrap

/-!
# Residual-based integration with a metric first-exit argument

An approximate curve in the proved inner tube and its finite differential
residual certify the actual clipped solution's error and original-field tube.
No hypothesis that the actual solution already remains in the tube is needed.
-/
namespace CentroidEscape.MetricStability
noncomputable section
open Set Real
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

lemma metricNorm_neg (h : WeightedState) : metricNorm (-h)=metricNorm h := by
  simp [metricNorm,metricEnergy]

lemma exact_left_residual (x y v : WeightedState) :
    metricNorm ((weightedField x-v)-(weightedField x-weightedField y))=
      metricNorm (v-weightedField y) := by
  have he : (weightedField x-v)-(weightedField x-weightedField y)=-(v-weightedField y) := by
    ext i
    simp
  rw [he,metricNorm_neg]

theorem metric_residual_tube {f g g' : ℝ → WeightedState} {T δ : ℝ}
    (hT : 0≤T) (hδ : 0≤δ)
    (hf : ∀ t∈Icc 0 T, HasDerivAt f (clippedField (f t)) t)
    (hg : ContinuousOn g (Icc 0 T))
    (hgd : ∀ t∈Ico 0 T, HasDerivWithinAt g (g' t) (Ici t) t)
    (hgt : ∀ t∈Icc 0 T, g t∈innerWeightedTube)
    (hres : ∀ t∈Ico 0 T, metricNorm (g' t-weightedField (g t))≤δ)
    (hbudget : gronwallBound (metricNorm (f 0-g 0)) (39/20) δ T<1/2000) :
    (∀ t∈Icc 0 T, f t∈weightedTube) ∧
    (∀ t∈Icc 0 T, metricNorm (f t-g t)≤
      gronwallBound (metricNorm (f 0-g 0)) (39/20) δ t) := by
  have hfc : ContinuousOn f (Icc 0 T) := fun t ht=>(hf t ht).continuousAt.continuousWithinAt
  have hcmp (s : ℝ) (hs : s∈Icc 0 T) (htube : ∀ t∈Ico 0 s, f t∈weightedTube) :
      ∀ t∈Icc 0 s, metricNorm (f t-g t)≤
        gronwallBound (metricNorm (f 0-g 0)) (39/20) δ t := by
    have he := metric_approx_trajectories hs.1 hδ
      (hfc.mono (Icc_subset_Icc le_rfl hs.2)) (hg.mono (Icc_subset_Icc le_rfl hs.2))
      (fun t ht=>by
        have hd := hf t ⟨ht.1,ht.2.le.trans hs.2⟩
        rw [clippedField_eq (htube t ht)] at hd
        exact hd.hasDerivWithinAt)
      (fun t ht=>hgd t ⟨ht.1,ht.2.trans_le hs.2⟩)
      htube (fun t ht=>innerWeightedTube_subset (hgt t ⟨ht.1,ht.2.le.trans hs.2⟩))
      (fun t ht=>by
        rw [exact_left_residual]
        exact hres t ⟨ht.1,ht.2.trans_le hs.2⟩)
    simpa only [sub_zero] using he
  have hnear : ∀ t∈Icc 0 T, metricNorm (f t-g t)<1/2000 := by
    by_contra hnot
    push Not at hnot
    have hc : ContinuousOn (fun t=>metricNorm (f t-g t)) (Icc 0 T) :=
      Real.continuous_sqrt.comp_continuousOn (metricEnergy_continuousOn (hfc.sub hg))
    obtain ⟨s,hs,hlarge,hbefore⟩ := exists_first_threshold hc hnot
    have hstube : ∀ t∈Ico 0 s, f t∈weightedTube :=
      fun t ht=>tube_of_metric_near_inner (hgt t ⟨ht.1,ht.2.le.trans hs.2⟩) (hbefore t ht)
    have hc := hcmp s hs hstube s ⟨hs.1,le_rfl⟩
    have hm := gronwallBound_mono (metricNorm_nonneg (f 0-g 0)) hδ
      (by norm_num : (0:ℝ)≤39/20) hs.2
    linarith
  have htube : ∀ t∈Icc 0 T, f t∈weightedTube :=
    fun t ht=>tube_of_metric_near_inner (hgt t ht) (hnear t ht)
  exact ⟨htube,hcmp T ⟨hT,le_rfl⟩ (fun t ht=>htube t (Ico_subset_Icc_self ht))⟩

/-- Directly accepts the old weighted-sup residual bound; factor 34 is injected
once in the forcing, and the resulting error remains in the metric. -/
theorem metric_residual_tube_of_weighted {f g g' : ℝ → WeightedState} {T R : ℝ}
    (hT : 0≤T) (hR : 0≤R)
    (hf : ∀ t∈Icc 0 T, HasDerivAt f (clippedField (f t)) t)
    (hg : ContinuousOn g (Icc 0 T))
    (hgd : ∀ t∈Ico 0 T, HasDerivWithinAt g (g' t) (Ici t) t)
    (hgt : ∀ t∈Icc 0 T, g t∈innerWeightedTube)
    (hres : ∀ t∈Ico 0 T, ‖g' t-weightedField (g t)‖≤R)
    (hbudget : gronwallBound (metricNorm (f 0-g 0)) (39/20) (34*R) T<1/2000) :
    (∀ t∈Icc 0 T, f t∈weightedTube) ∧
    (∀ t∈Icc 0 T, metricNorm (f t-g t)≤
      gronwallBound (metricNorm (f 0-g 0)) (39/20) (34*R) t) := by
  apply metric_residual_tube hT (by positivity) hf hg hgd hgt ?_ hbudget
  intro t ht
  exact (metricNorm_le_weightedNorm _).trans (mul_le_mul_of_nonneg_left (hres t ht) (by norm_num))

end
end CentroidEscape.MetricStability

#print axioms CentroidEscape.MetricStability.metric_residual_tube_of_weighted

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape.MetricStability).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Metric residual first-exit audit passed for {checked} declarations."
