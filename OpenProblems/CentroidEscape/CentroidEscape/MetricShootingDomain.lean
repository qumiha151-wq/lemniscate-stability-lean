import CentroidEscape.ShootingDomain
import CentroidEscape.MetricShootingMaps

namespace CentroidEscape.MetricStability
noncomputable section
open Set Real
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

lemma tube_of_metric_near_margin {a b : WeightedState} {δ : ℝ}
    (ha : ∀ i, i≠6 → |a i|≤tubeRadius i-δ) (hab : metricNorm (b-a)<δ) :
    b∈weightedTube := by
  have hn := (weightedNorm_le_metricNorm (b-a)).trans_lt hab
  intro i hi
  have hc : |b i-a i|≤‖b-a‖ := by
    simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (b-a) i
  have hh := abs_add_le (b i-a i) (a i)
  rw [sub_add_cancel] at hh
  linarith [ha i hi]

/-- The metric first-exit proof with an arbitrary positive reference margin.
It applies to the ACTUAL short extension, whose margin differs from the
original checked inner tube. -/
theorem shootingFlow_metric_neighborhood_margin (T : ℝ) (hT : 0≤T)
    {a b : WeightedState} {δ : ℝ} (hδ : 0<δ)
    (ha : ∀ t∈Icc 0 T, ∀ i, i≠6 → |shootingFlow T hT t a i|≤tubeRadius i-δ)
    (hab : metricNorm (b-a)*exp ((39/20)*T)<δ) :
    (∀ t∈Icc 0 T, shootingFlow T hT t b∈weightedTube) ∧
    (∀ t∈Icc 0 T, metricNorm (shootingFlow T hT t b-shootingFlow T hT t a)≤
      metricNorm (b-a)*exp ((39/20)*t)) := by
  let f : ℝ → WeightedState := fun t=>shootingFlow T hT t b
  let g : ℝ → WeightedState := fun t=>shootingFlow T hT t a
  have hf : ContinuousOn f (Icc 0 T) :=
    fun t ht=>(shootingFlow_derivative T hT b ht).continuousAt.continuousWithinAt
  have hg : ContinuousOn g (Icc 0 T) :=
    fun t ht=>(shootingFlow_derivative T hT a ht).continuousAt.continuousWithinAt
  have hgT : ∀ t∈Icc 0 T, g t∈weightedTube := by
    intro t ht i hi
    have hh := ha t ht i hi
    change |g t i|≤_ at hh
    linarith
  have hnear : ∀ t∈Icc 0 T, metricNorm (f t-g t)<δ := by
    by_contra hnot
    push Not at hnot
    have hc : ContinuousOn (fun t=>metricNorm (f t-g t)) (Icc 0 T) :=
      Real.continuous_sqrt.comp_continuousOn (metricEnergy_continuousOn (hf.sub hg))
    obtain ⟨s,hs,hlarge,hbefore⟩ := exists_first_threshold hc hnot
    have hsmalltube : ∀ t∈Ico 0 s, f t∈weightedTube := by
      intro t ht
      exact tube_of_metric_near_margin (ha t ⟨ht.1,ht.2.le.trans hs.2⟩) (hbefore t ht)
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
    fun t ht=>tube_of_metric_near_margin (ha t ht) (hnear t ht)
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

def metricShootingRadius (T : ℝ) : ℝ :=
  (3/272000)*exp (-(39/20)*shootingExtendedHorizon T)

lemma metricShootingRadius_pos (T : ℝ) : 0<metricShootingRadius T := by
  unfold metricShootingRadius
  positivity

/-- A usable exp(-KT) open neighborhood for the true extended flow, proved
by first exit and the reference's explicit 3/8000 extension margin. -/
theorem shootingFlow_extended_metric_tube (T : ℝ) (hT : 0≤T) {c : WeightedState}
    (hc : ∀ t∈Icc 0 T, shootingFlow T hT t c∈innerWeightedTube) :
    ShootingTubeNeighborhood (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT)
      c (metricShootingRadius T) := by
  intro b hb
  apply (shootingFlow_metric_neighborhood_margin _ _ (by norm_num : (0:ℝ)<3/8000)
    (shootingFlow_extended_reference_margin T hT hc) ?_).1
  calc
    metricNorm (b-c)*exp ((39/20)*shootingExtendedHorizon T) ≤
        34*dist b c*exp ((39/20)*shootingExtendedHorizon T) := by
      rw [dist_eq_norm]
      exact mul_le_mul_of_nonneg_right (metricNorm_le_weightedNorm (b-c)) (exp_pos _).le
    _ < 34*metricShootingRadius T*exp ((39/20)*shootingExtendedHorizon T) := by
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hb (by norm_num)) (exp_pos _)
    _ = 3/8000 := by
      rw [metricShootingRadius]
      calc
        _ = (34*(3/272000:ℝ))*(exp (-(39/20)*shootingExtendedHorizon T)*
            exp ((39/20)*shootingExtendedHorizon T)) := by ring
        _ = _ := by rw [← exp_add]; ring_nf; norm_num

def metricShootingParameterRadius (T : ℝ) : ℝ :=
  min (metricShootingRadius T/4) (min (T/2) (1/32000))

lemma metricShootingParameterRadius_pos {T : ℝ} (hT : 0<T) : 0<metricShootingParameterRadius T := by
  unfold metricShootingParameterRadius
  exact lt_min (div_pos (metricShootingRadius_pos _) (by norm_num))
    (lt_min (by positivity) (by norm_num))

theorem metricShootingParameterRadius_domain {T : ℝ} {p₀ p : Fin 3 → ℝ}
    (hcenter : p₀ 2=T) (hp : p∈Metric.ball p₀ (metricShootingParameterRadius T)) :
    p 2∈Ioo 0 (shootingExtendedHorizon T) ∧
      shootingInitial p∈Metric.ball (shootingInitial p₀) (metricShootingRadius T/4) := by
  have hd : dist p p₀<metricShootingParameterRadius T := hp
  have ht : |p 2-T|≤dist p p₀ := by
    simpa only [dist_eq_norm,Pi.sub_apply,Real.norm_eq_abs,hcenter] using norm_le_pi_norm (p-p₀) 2
  have hinit : dist (shootingInitial p) (shootingInitial p₀)≤dist p p₀ := by
    simpa only [NNReal.coe_one,one_mul] using shootingInitial_lipschitz.dist_le_mul p p₀
  have hR := min_le_left (metricShootingRadius T/4) (min (T/2) (1/32000:ℝ))
  have htR : metricShootingParameterRadius T≤T/2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hdR : metricShootingParameterRadius T≤1/32000 :=
    (min_le_right _ _).trans (min_le_right _ _)
  constructor
  · constructor
    · have hn := (abs_le.mp ht).1
      linarith [dist_nonneg (x:=p) (y:=p₀)]
    · have hn := (abs_le.mp ht).2
      unfold shootingExtendedHorizon
      linarith
  · change dist _ _ < _
    change metricShootingParameterRadius T≤_ at hR
    linarith

theorem actualShootingMap_hasFDerivAt_metric_extended {T : ℝ} (hT : 0<T) {p₀ : Fin 3 → ℝ}
    (hcenter : p₀ 2=T)
    (hc : ∀ t∈Icc 0 T, shootingFlow T hT.le t (shootingInitial p₀)∈innerWeightedTube)
    {p : Fin 3 → ℝ} (hp : p∈Metric.ball p₀ (metricShootingParameterRadius T)) :
    HasFDerivAt (actualShootingMap (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT.le))
      (actualShootingDifferential (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT.le) p) p := by
  have hdom := metricShootingParameterRadius_domain hcenter hp
  exact actualShootingMap_hasFDerivAt _ _ (metricShootingRadius_pos _)
    (shootingFlow_extended_metric_tube T hT.le hc) hdom.1 hdom.2

end
end CentroidEscape.MetricStability

#print axioms CentroidEscape.MetricStability.actualShootingMap_hasFDerivAt_metric_extended

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Metric shooting-domain audit passed for {checked} declarations."
