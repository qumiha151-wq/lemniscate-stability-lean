import CentroidEscape.HigherRegularity
import CentroidEscape.MetricShootingJacobian

namespace CentroidEscape
noncomputable section
open Set Real Filter
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def weightedProfile (w : WeightedState) : State :=
  ![w 0,w 1,4*w 2,4*w 3,16*w 4,64*w 5]

lemma weightedProfile_hasDerivAt {w : ℝ → WeightedState} {s : ℝ}
    (hw : HasDerivAt w (weightedField (w s)) s) :
    HasDerivAt (fun t=>weightedProfile (w t)) (field (weightedProfile (w s))) s := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [weightedProfile,field,weightedField] using hasDerivAt_pi.mp hw 0
  · simpa [weightedProfile,field,weightedField] using hasDerivAt_pi.mp hw 1
  · convert! (hasDerivAt_pi.mp hw 2).const_mul 4 using 1
    simp [weightedProfile,field,weightedField]
    ring
  · convert! (hasDerivAt_pi.mp hw 3).const_mul 4 using 1
    simp [weightedProfile,field,weightedField]
    ring
  · convert! (hasDerivAt_pi.mp hw 4).const_mul 16 using 1
    simp [weightedProfile,field,weightedField]
    ring
  · convert! (hasDerivAt_pi.mp hw 5).const_mul 64 using 1
    simp [weightedProfile,field,weightedField]
    ring

lemma weightedProfile_initial (p : Fin 3 → ℝ) :
    weightedProfile (shootingInitial p)=![p 0,0,0,1,p 1,0] := by
  ext i
  fin_cases i <;> simp [weightedProfile,shootingInitial]
  ring

lemma weightedProfile_shooting_fixed {a : WeightedState} (ha : shootingProjection a=0) :
    reverseState (weightedProfile a)=weightedProfile a := by
  apply shooting_fixed
  · simpa [shootingProjection,weightedProfile] using congr_fun ha 0
  · simpa [shootingProjection,weightedProfile] using congr_fun ha 1
  · simpa [shootingProjection,weightedProfile] using congr_fun ha 2

/-- A true weighted shooting zero with positive moment produces the already
constructed jointly smooth, immersed, classical FEF with escaping centroid.
The geometric force here is the actual intrinsic force of the resulting curve. -/
theorem weighted_shooting_data_yields_smooth_classical_FEF_escape
    {w : ℝ → WeightedState} {p : Fin 3 → ℝ} {L : ℝ} (hL : 0<L)
    (hw : ∀s∈Icc 0 L, HasDerivAt w (weightedField (w s)) s)
    (hw0 : w 0=shootingInitial p) (hend : shootingProjection (w L)=0)
    (hmoment : 0<w L 6) :
    ∃ γ : ℝ → ℝ → Plane,
      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ=>γ q.1 q.2) {q | -1/4<q.1} ∧
      (∀t, Function.Periodic (γ t) (2*L) ∧ ContDiff ℝ ∞ (γ t)) ∧
      (∀t, 0≤t → ∀s, 0<‖deriv (γ t) s‖) ∧
      (∀t, 0≤t → ∀s, HasDerivAt (fun r=>γ r s)
        ((-curveElasticForce (γ t) s) • curveUnitNormal (γ t) s) t) ∧
      Tendsto (fun t=>curveCentroidX (2*L) (γ t)) atTop atTop := by
  apply exact_half_orbit_yields_smooth_classical_FEF_escape
    (z:=fun s=>weightedProfile (w s)) (m:=fun s=>w s 6) hL
  · exact fun s hs=>weightedProfile_hasDerivAt (hw s hs)
  · rw [hw0,weightedProfile_initial]
    apply shooting_fixed <;> simp
  · exact weightedProfile_shooting_fixed hend
  · simp [hw0,weightedProfile_initial]
  · simp [hw0,weightedProfile_initial]
  · intro s hs
    simpa [weightedField,weightedProfile] using hasDerivAt_pi.mp (hw s hs) 6
  · simp [hw0,shootingInitial]
  · exact hmoment

/-- The ACTUAL finite-horizon shooting map supplies all half-orbit equations;
only its exact zero and positive terminal moment are needed in addition to
the trajectory region already proved by the checked grid and extension. -/
theorem actual_shooting_zero_yields_smooth_classical_FEF_escape
    (U : ℝ) (hU : 0≤U) {p : Fin 3 → ℝ} (hp : p 2∈Ioo 0 U)
    (htube : ∀s∈Icc 0 U, shootingFlow U hU s (shootingInitial p)∈weightedTube)
    (hroot : actualShootingMap U hU p=0)
    (hmoment : 0<shootingFlow U hU (p 2) (shootingInitial p) 6) :
    ∃ γ : ℝ → ℝ → Plane,
      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ=>γ q.1 q.2) {q | -1/4<q.1} ∧
      (∀t, Function.Periodic (γ t) (2*p 2) ∧ ContDiff ℝ ∞ (γ t)) ∧
      (∀t, 0≤t → ∀s, 0<‖deriv (γ t) s‖) ∧
      (∀t, 0≤t → ∀s, HasDerivAt (fun r=>γ r s)
        ((-curveElasticForce (γ t) s) • curveUnitNormal (γ t) s) t) ∧
      Tendsto (fun t=>curveCentroidX (2*p 2) (γ t)) atTop atTop := by
  apply weighted_shooting_data_yields_smooth_classical_FEF_escape hp.1
    (w:=fun s=>shootingFlow U hU s (shootingInitial p)) (p:=p)
  · intro s hs
    have hsmem : s∈Icc 0 U := ⟨hs.1,hs.2.trans hp.2.le⟩
    simpa only [clippedField_eq (htube s hsmem)] using shootingFlow_derivative U hU (shootingInitial p) hsmem
  · exact shootingFlow_zero U hU (shootingInitial p)
  · exact hroot
  · exact hmoment

def actualShootingMoment (U : ℝ) (hU : 0≤U) (p : Fin 3 → ℝ) : ℝ :=
  shootingFlow U hU (p 2) (shootingInitial p) 6

theorem actualShootingMoment_difference (U : ℝ) (hU : 0≤U)
    {p₀ : Fin 3 → ℝ} {R : ℝ} (hreg : ShootingTubeNeighborhood U hU (shootingInitial p₀) R)
    {p q : Fin 3 → ℝ} (hp : p∈Metric.ball p₀ R) (hq : q∈Metric.ball p₀ R)
    (hpt : p 2∈Icc 0 U) (hqt : q 2∈Icc 0 U) :
    |actualShootingMoment U hU p-actualShootingMoment U hU q| ≤
      ((13/8:ℝ)*exp ((39/20)*U)+2)*dist p q := by
  have hpT := hreg _ (MetricStability.shootingInitial_mem_ball hp)
  have hqT := hreg _ (MetricStability.shootingInitial_mem_ball hq)
  have hmetric := MetricStability.shootingFlow_metric_distance_region U hU hpT hqT (p 2) hpt
  have hinit := MetricStability.shootingInitial_metric_bound p q
  have he := exp_le_exp.mpr (show (39/20)*(p 2)≤(39/20)*U by linarith [hpt.2])
  have hm := mul_le_mul hinit he (exp_pos _).le (by positivity)
  have hn := MetricStability.weightedNorm_le_metricNorm
    (shootingFlow U hU (p 2) (shootingInitial p)-shootingFlow U hU (p 2) (shootingInitial q))
  have ht := (shootingFlow_time_lipschitz U hU (shootingInitial q)).dist_le_mul (p 2) hpt (q 2) hqt
  have htime : dist (p 2) (q 2)≤dist p q := by
    simpa only [dist_eq_norm,Pi.sub_apply] using norm_le_pi_norm (p-q) 2
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (shootingFlow U hU (p 2) (shootingInitial p))
    (shootingFlow U hU (p 2) (shootingInitial q))
    (shootingFlow U hU (q 2) (shootingInitial q))
  have hc := norm_le_pi_norm
    (shootingFlow U hU (p 2) (shootingInitial p)-shootingFlow U hU (q 2) (shootingInitial q)) 6
  simp only [dist_eq_norm,NNReal.coe_ofNat] at ht htime ⊢
  simp only [Pi.sub_apply,Real.norm_eq_abs] at hc
  unfold actualShootingMoment
  nlinarith

theorem actualShootingMoment_positive_near_center {T : ℝ} (hT : 0<T) (hTmin : 1≤T)
    (hbudget : shootingExtendedHorizon T≤15/2) {p₀ : Fin 3 → ℝ} (hcenter : p₀ 2=T)
    (hc : ∀t∈Icc 0 T, shootingFlow T hT.le t (shootingInitial p₀)∈innerWeightedTube)
    {r : ℝ} (hrR : r<1/10^13)
    (hmoment : (7000000:ℝ)*r<shootingFlow T hT.le T (shootingInitial p₀) 6)
    {p : Fin 3 → ℝ} (hp : p∈Metric.closedBall p₀ r) :
    0<actualShootingMoment (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT.le) p := by
  have hRadius := MetricStability.metricShootingParameterRadius_lower_bound hTmin hbudget
  have hpball : p∈Metric.ball p₀ (MetricStability.metricShootingParameterRadius T) :=
    lt_of_le_of_lt hp (hrR.trans hRadius)
  have hdom := MetricStability.metricShootingParameterRadius_domain hcenter hpball
  have hR := MetricStability.metricShootingRadius_pos T
  have hpR : p∈Metric.ball p₀ (MetricStability.metricShootingRadius T) := by
    have hsmall : dist p p₀<MetricStability.metricShootingRadius T/4 :=
      (show dist p p₀<min (MetricStability.metricShootingRadius T/4) (min (T/2) (1/32000)) from hpball).trans_le
        (min_le_left _ _)
    change dist p p₀<MetricStability.metricShootingRadius T
    linarith
  have htcenter : p₀ 2∈Icc 0 (shootingExtendedHorizon T) := by
    rw [hcenter]
    exact ⟨hT.le,by unfold shootingExtendedHorizon; linarith⟩
  have hdiff := actualShootingMoment_difference _ _
    (MetricStability.shootingFlow_extended_metric_tube T hT.le hc)
    hpR (Metric.mem_ball_self hR) ⟨hdom.1.1.le,hdom.1.2.le⟩ htcenter
  have he := MetricStability.metric_exp_budget hbudget
  have hcoef : (13/8:ℝ)*exp ((39/20)*shootingExtendedHorizon T)+2≤7000000 := by linarith
  have hprod := mul_le_mul_of_nonneg_right hcoef (dist_nonneg (x:=p) (y:=p₀))
  have hdist : dist p p₀≤r := hp
  have hbase : actualShootingMoment (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT.le) p₀=
      shootingFlow T hT.le T (shootingInitial p₀) 6 := by
    unfold actualShootingMoment
    rw [hcenter,shootingFlow_horizon_compatibility hT.le (shootingExtendedHorizon_nonneg hT.le)
      (show T≤shootingExtendedHorizon T by unfold shootingExtendedHorizon; linarith)
      (shootingInitial p₀) (right_mem_Icc.mpr hT.le)]
  rw [hbase] at hdiff
  have hlow := (abs_le.mp hdiff).1
  linarith

/-- The exact shooting zero produced in the Newton ball yields a classical
escaping flow. Positive moment is inferred from the center enclosure and a
proved 7,000,000*r variation budget, not postulated at the unknown root. -/
theorem nearby_shooting_zero_yields_smooth_classical_FEF_escape
    {T : ℝ} (hT : 0<T) (hTmin : 1≤T) (hbudget : shootingExtendedHorizon T≤15/2)
    {p₀ : Fin 3 → ℝ} (hcenter : p₀ 2=T)
    (hc : ∀t∈Icc 0 T, shootingFlow T hT.le t (shootingInitial p₀)∈innerWeightedTube)
    {r : ℝ} (hrR : r<1/10^13)
    (hmoment : (7000000:ℝ)*r<shootingFlow T hT.le T (shootingInitial p₀) 6)
    {p : Fin 3 → ℝ} (hp : p∈Metric.closedBall p₀ r)
    (hroot : actualShootingMap (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT.le) p=0) :
    ∃ γ : ℝ → ℝ → Plane,
      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ=>γ q.1 q.2) {q | -1/4<q.1} ∧
      (∀t, Function.Periodic (γ t) (2*p 2) ∧ ContDiff ℝ ∞ (γ t)) ∧
      (∀t, 0≤t → ∀s, 0<‖deriv (γ t) s‖) ∧
      (∀t, 0≤t → ∀s, HasDerivAt (fun r=>γ r s)
        ((-curveElasticForce (γ t) s) • curveUnitNormal (γ t) s) t) ∧
      Tendsto (fun t=>curveCentroidX (2*p 2) (γ t)) atTop atTop := by
  have hRadius := MetricStability.metricShootingParameterRadius_lower_bound hTmin hbudget
  have hpball : p∈Metric.ball p₀ (MetricStability.metricShootingParameterRadius T) :=
    lt_of_le_of_lt hp (hrR.trans hRadius)
  have hdom := MetricStability.metricShootingParameterRadius_domain hcenter hpball
  apply actual_shooting_zero_yields_smooth_classical_FEF_escape _ _ hdom.1 (hroot:=hroot)
  · apply MetricStability.shootingFlow_extended_metric_tube T hT.le hc
    have hR := MetricStability.metricShootingRadius_pos T
    have hh : dist (shootingInitial p) (shootingInitial p₀)<MetricStability.metricShootingRadius T/4 := hdom.2
    change dist (shootingInitial p) (shootingInitial p₀)<MetricStability.metricShootingRadius T
    linarith
  · exact actualShootingMoment_positive_near_center hT hTmin hbudget hcenter hc hrR hmoment hp

end
end CentroidEscape

#print axioms CentroidEscape.actual_shooting_zero_yields_smooth_classical_FEF_escape
#print axioms CentroidEscape.actualShootingMoment_positive_near_center
#print axioms CentroidEscape.nearby_shooting_zero_yields_smooth_classical_FEF_escape

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked+1
  logInfo m!"Shooting geometry bridge audit passed for {checked} declarations."
