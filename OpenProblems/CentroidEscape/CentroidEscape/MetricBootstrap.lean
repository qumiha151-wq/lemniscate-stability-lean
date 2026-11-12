import CentroidEscape.MetricFlow
import CentroidEscape.ShootingVariation
import Mathlib.Topology.Order.Compact

/-!
# A metric first-exit bootstrap for the actual shooting flow

The globally constructed clipped flow is only an existence device. The
one-sided metric bound is invoked strictly before the first possible exit;
the resulting strict margin proves that no exit occurs.
-/
namespace CentroidEscape.MetricStability
noncomputable section
open Set Real
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

lemma exists_first_threshold {W : ℝ → ℝ} {T c : ℝ}
    (hc : ContinuousOn W (Icc 0 T)) (hbad : ∃ t∈Icc 0 T, c≤W t) :
    ∃ s∈Icc 0 T, c≤W s ∧ ∀ t∈Ico 0 s, W t<c := by
  let S : Set ℝ := Icc 0 T ∩ W ⁻¹' Ici c
  have hclosed : IsClosed S := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed (fun _ h=>h.1)
  have hne : S.Nonempty := by
    rcases hbad with ⟨t,ht,hc⟩
    exact ⟨t,ht,hc⟩
  obtain ⟨s,hs,hmin⟩ := hcompact.exists_isMinOn hne continuousOn_id
  refine ⟨s,hs.1,hs.2,?_⟩
  intro t ht
  by_contra hnot
  have htS : t∈S := ⟨⟨ht.1,ht.2.le.trans hs.1.2⟩,le_of_not_gt hnot⟩
  have hst : s≤t := hmin htS
  linarith [ht.2]

lemma tube_of_metric_near_inner {a b : WeightedState} (ha : a∈innerWeightedTube)
    (hab : metricNorm (b-a)<1/2000) : b∈weightedTube := by
  have hn : ‖b-a‖<1/2000 := (weightedNorm_le_metricNorm (b-a)).trans_lt hab
  intro i hi
  have hc : |b i-a i|≤‖b-a‖ := by
    simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (b-a) i
  have habs := abs_add_le (b i-a i) (a i)
  rw [sub_add_cancel] at habs
  linarith [ha i hi]

/-- A uniform original-field neighborhood with exp(-(39/20)T) scaling. -/
theorem shootingFlow_metric_neighborhood (T : ℝ) (hT : 0≤T) {a b : WeightedState}
    (ha : ∀ t∈Icc 0 T, shootingFlow T hT t a∈innerWeightedTube)
    (hab : metricNorm (b-a)*exp ((39/20)*T)<1/2000) :
    (∀ t∈Icc 0 T, shootingFlow T hT t b∈weightedTube) ∧
    (∀ t∈Icc 0 T, metricNorm (shootingFlow T hT t b-shootingFlow T hT t a)≤
      metricNorm (b-a)*exp ((39/20)*t)) := by
  let f : ℝ → WeightedState := fun t=>shootingFlow T hT t b
  let g : ℝ → WeightedState := fun t=>shootingFlow T hT t a
  have hf : ContinuousOn f (Icc 0 T) :=
    fun t ht=>(shootingFlow_derivative T hT b ht).continuousAt.continuousWithinAt
  have hg : ContinuousOn g (Icc 0 T) :=
    fun t ht=>(shootingFlow_derivative T hT a ht).continuousAt.continuousWithinAt
  have hgT : ∀ t∈Icc 0 T, g t∈weightedTube := fun t ht=>innerWeightedTube_subset (ha t ht)
  have hnear : ∀ t∈Icc 0 T, metricNorm (f t-g t)<1/2000 := by
    by_contra hnot
    push Not at hnot
    have hc : ContinuousOn (fun t=>metricNorm (f t-g t)) (Icc 0 T) :=
      Real.continuous_sqrt.comp_continuousOn (metricEnergy_continuousOn (hf.sub hg))
    obtain ⟨s,hs,hlarge,hbefore⟩ := exists_first_threshold hc hnot
    have hsmalltube : ∀ t∈Ico 0 s, f t∈weightedTube := by
      intro t ht
      exact tube_of_metric_near_inner (ha t ⟨ht.1,ht.2.le.trans hs.2⟩) (hbefore t ht)
    have hcompare := metric_exact_trajectories hs.1
      (hf.mono (Icc_subset_Icc le_rfl hs.2)) (hg.mono (Icc_subset_Icc le_rfl hs.2))
      (fun t ht=> by
        have hd := shootingFlow_derivative T hT b ⟨ht.1,ht.2.le.trans hs.2⟩
        change HasDerivAt f (clippedField (f t)) t at hd
        rw [clippedField_eq (hsmalltube t ht)] at hd
        exact hd.hasDerivWithinAt)
      (fun t ht=> by
        have htT : t∈Icc 0 T := ⟨ht.1,ht.2.le.trans hs.2⟩
        have hd := shootingFlow_derivative T hT a htT
        change HasDerivAt g (clippedField (g t)) t at hd
        rw [clippedField_eq (hgT t htT)] at hd
        exact hd.hasDerivWithinAt)
      hsmalltube (fun t ht=>hgT t ⟨ht.1,ht.2.le.trans hs.2⟩) s ⟨hs.1,le_rfl⟩
    have he : metricNorm (f s-g s)≤metricNorm (b-a)*exp ((39/20)*s) := by
      simpa only [f,g,shootingFlow_zero,sub_zero] using hcompare
    have hexp : exp ((39/20)*s)≤exp ((39/20)*T) := exp_le_exp.mpr (by linarith [hs.2])
    have hupper := he.trans (mul_le_mul_of_nonneg_left hexp (metricNorm_nonneg (b-a)))
    linarith
  have hfT : ∀ t∈Icc 0 T, f t∈weightedTube :=
    fun t ht=>tube_of_metric_near_inner (ha t ht) (hnear t ht)
  refine ⟨hfT,?_⟩
  have hcompare := metric_exact_trajectories hT hf hg
    (fun t ht=>by
      have htT := Ico_subset_Icc_self ht
      have hd := shootingFlow_derivative T hT b htT
      change HasDerivAt f (clippedField (f t)) t at hd
      rw [clippedField_eq (hfT t htT)] at hd
      exact hd.hasDerivWithinAt)
    (fun t ht=>by
      have htT := Ico_subset_Icc_self ht
      have hd := shootingFlow_derivative T hT a htT
      change HasDerivAt g (clippedField (g t)) t at hd
      rw [clippedField_eq (hgT t htT)] at hd
      exact hd.hasDerivWithinAt)
    (fun t ht=>hfT t (Ico_subset_Icc_self ht)) (fun t ht=>hgT t (Ico_subset_Icc_self ht))
  simpa only [f,g,shootingFlow_zero,sub_zero] using hcompare

end
end CentroidEscape.MetricStability

#print axioms CentroidEscape.MetricStability.shootingFlow_metric_neighborhood

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
  logInfo m!"Metric first-exit audit passed for {checked} declarations."
