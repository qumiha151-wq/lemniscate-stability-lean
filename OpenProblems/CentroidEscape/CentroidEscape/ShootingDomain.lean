import CentroidEscape.ShootingJacobian

/-!
# Actual open time/parameter domain beyond a checked endpoint

A checked interior trajectory is extended by 1/16000 using the globally
bounded actual clipped flow. Its speed bound leaves a positive tube margin.
This supplies an honest open neighborhood for differentiating terminal time.
-/
namespace CentroidEscape
noncomputable section
open Set Real Filter
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem shootingFlow_horizon_compatibility {T U : ℝ} (hT : 0≤T) (hU : 0≤U)
    (hTU : T≤U) (a : WeightedState) {t : ℝ} (ht : t∈Icc 0 T) :
    shootingFlow U hU t a=shootingFlow T hT t a := by
  exact shootingFlow_unique T hT (shootingFlow_zero U hU a)
    (fun s hs => shootingFlow_derivative U hU a ⟨hs.1,hs.2.trans hTU⟩) ht

def shootingExtendedHorizon (T : ℝ) : ℝ := T+1/16000

lemma shootingExtendedHorizon_nonneg {T : ℝ} (hT : 0≤T) : 0≤shootingExtendedHorizon T := by
  unfold shootingExtendedHorizon
  linarith

/-- The short extension and nearby actual trajectories remain in the
original polynomial region, deduced from the checked reference margin. -/
theorem shootingFlow_extended_tube (T : ℝ) (hT : 0≤T) {c : WeightedState}
    (hc : ∀ t∈Icc 0 T, shootingFlow T hT t c∈innerWeightedTube) :
    ShootingTubeNeighborhood (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT)
      c (shootingNeighborhoodRadius (shootingExtendedHorizon T)) := by
  let U := shootingExtendedHorizon T
  let hU : 0≤U := shootingExtendedHorizon_nonneg hT
  have hTU : T≤U := by dsimp [U,shootingExtendedHorizon]; linarith
  intro b hb t ht
  have hd := shootingFlow_near_reference U hU hb ht
  by_cases htle : t≤T
  · have he := shootingFlow_horizon_compatibility hT hU hTU c ⟨ht.1,htle⟩
    rw [he] at hd
    exact weightedTube_mem_of_near_inner (hc t ⟨ht.1,htle⟩) (by linarith)
  · have hTmem : T∈Icc 0 U := ⟨hT,hTU⟩
    have htime := (shootingFlow_time_lipschitz U hU c).dist_le_mul t ht T hTmem
    rw [Real.dist_eq,abs_of_nonneg (by linarith : 0≤t-T)] at htime
    norm_num only [NNReal.coe_ofNat] at htime
    have he := shootingFlow_horizon_compatibility hT hU hTU c (right_mem_Icc.mpr hT)
    rw [he] at htime
    have htri := dist_triangle (shootingFlow U hU t b) (shootingFlow U hU t c)
      (shootingFlow T hT T c)
    apply weightedTube_mem_of_near_inner (hc T (right_mem_Icc.mpr hT))
    have hmax : t≤T+1/16000 := ht.2
    linarith

theorem shootingFlow_extended_original (T : ℝ) (hT : 0≤T) {c : WeightedState}
    (hc : ∀ t∈Icc 0 T, shootingFlow T hT t c∈innerWeightedTube)
    {b : WeightedState} (hb : b∈Metric.ball c (shootingNeighborhoodRadius (shootingExtendedHorizon T))) :
    ∀ t∈Icc 0 (shootingExtendedHorizon T),
      HasDerivAt (fun s => shootingFlow (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT) s b)
        (weightedField (shootingFlow (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT) t b)) t := by
  intro t ht
  have hreg := shootingFlow_extended_tube T hT hc b hb t ht
  simpa only [clippedField_eq hreg] using
    shootingFlow_derivative (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT) b ht

def shootingParameterRadius (T : ℝ) : ℝ :=
  min (shootingNeighborhoodRadius (shootingExtendedHorizon T)/4) (min (T/2) (1/32000))

lemma shootingParameterRadius_pos {T : ℝ} (hT : 0<T) : 0<shootingParameterRadius T := by
  unfold shootingParameterRadius
  exact lt_min (div_pos (shootingNeighborhoodRadius_pos _) (by norm_num))
    (lt_min (by positivity) (by norm_num))

theorem shootingParameterRadius_domain {T : ℝ} {p₀ p : Fin 3 → ℝ}
    (hcenter : p₀ 2=T) (hp : p∈Metric.ball p₀ (shootingParameterRadius T)) :
    p 2∈Ioo 0 (shootingExtendedHorizon T) ∧
      shootingInitial p∈Metric.ball (shootingInitial p₀)
        (shootingNeighborhoodRadius (shootingExtendedHorizon T)/4) := by
  have hd : dist p p₀<shootingParameterRadius T := hp
  have ht : |p 2-T|≤dist p p₀ := by
    simpa only [dist_eq_norm,Pi.sub_apply,Real.norm_eq_abs,hcenter] using norm_le_pi_norm (p-p₀) 2
  have hinit : dist (shootingInitial p) (shootingInitial p₀)≤dist p p₀ := by
    simpa only [NNReal.coe_one,one_mul] using shootingInitial_lipschitz.dist_le_mul p p₀
  have hR := min_le_left (shootingNeighborhoodRadius (shootingExtendedHorizon T)/4) (min (T/2) (1/32000:ℝ))
  have htR : shootingParameterRadius T≤T/2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hdR : shootingParameterRadius T≤1/32000 :=
    (min_le_right _ _).trans (min_le_right _ _)
  constructor
  · constructor
    · have hn := (abs_le.mp ht).1
      linarith [dist_nonneg (x:=p) (y:=p₀)]
    · have hn := (abs_le.mp ht).2
      unfold shootingExtendedHorizon
      linarith
  · change dist _ _ < _
    change shootingParameterRadius T≤_ at hR
    linarith

/-- A checked interior reference yields a genuine open three-parameter
domain, including both signs of the variation in the terminal time L. -/
theorem actualShootingMap_hasFDerivAt_extended {T : ℝ} (hT : 0<T) {p₀ : Fin 3 → ℝ}
    (hcenter : p₀ 2=T)
    (hc : ∀ t∈Icc 0 T, shootingFlow T hT.le t (shootingInitial p₀)∈innerWeightedTube)
    {p : Fin 3 → ℝ} (hp : p∈Metric.ball p₀ (shootingParameterRadius T)) :
    HasFDerivAt (actualShootingMap (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT.le))
      (actualShootingDifferential (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT.le) p) p := by
  have hdom := shootingParameterRadius_domain hcenter hp
  exact actualShootingMap_hasFDerivAt _ _ (shootingNeighborhoodRadius_pos _)
    (shootingFlow_extended_tube T hT.le hc) hdom.1 hdom.2

theorem actualShootingMap_fderiv_variation_extended {T : ℝ} (hT : 0<T) {p₀ : Fin 3 → ℝ}
    (hcenter : p₀ 2=T)
    (hc : ∀ t∈Icc 0 T, shootingFlow T hT.le t (shootingInitial p₀)∈innerWeightedTube)
    {p q : Fin 3 → ℝ} (hp : p∈Metric.ball p₀ (shootingParameterRadius T))
    (hq : q∈Metric.ball p₀ (shootingParameterRadius T)) :
    ‖fderiv ℝ (actualShootingMap (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT.le)) p-
      fderiv ℝ (actualShootingMap (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT.le)) q‖ ≤
        64*shootingJacobianVariationBound (shootingExtendedHorizon T)*dist p q := by
  have hp' := shootingParameterRadius_domain hcenter hp
  have hq' := shootingParameterRadius_domain hcenter hq
  exact actualShootingMap_fderiv_variation _ _ (shootingNeighborhoodRadius_pos _)
    (shootingFlow_extended_tube T hT.le hc) hp'.1 hq'.1 hp'.2 hq'.2

/-- The reference itself retains a quantified margin during the extension.
This can feed a sharper metric first-exit argument with a variable margin. -/
theorem shootingFlow_extended_reference_margin (T : ℝ) (hT : 0≤T) {c : WeightedState}
    (hc : ∀ t∈Icc 0 T, shootingFlow T hT t c∈innerWeightedTube) :
    ∀ t∈Icc 0 (shootingExtendedHorizon T), ∀ i, i≠6 →
      |shootingFlow (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT) t c i| ≤
        tubeRadius i-3/8000 := by
  let U := shootingExtendedHorizon T
  let hU : 0≤U := shootingExtendedHorizon_nonneg hT
  have hTU : T≤U := by dsimp [U,shootingExtendedHorizon]; linarith
  intro t ht i hi
  by_cases htle : t≤T
  · rw [shootingFlow_horizon_compatibility hT hU hTU c ⟨ht.1,htle⟩]
    linarith [hc t ⟨ht.1,htle⟩ i hi]
  · have htime := (shootingFlow_time_lipschitz U hU c).dist_le_mul t ht T ⟨hT,hTU⟩
    rw [Real.dist_eq,abs_of_nonneg (by linarith : 0≤t-T)] at htime
    norm_num only [NNReal.coe_ofNat] at htime
    rw [shootingFlow_horizon_compatibility hT hU hTU c (right_mem_Icc.mpr hT)] at htime
    have hcoord : |shootingFlow U hU t c i-shootingFlow T hT T c i| ≤
        dist (shootingFlow U hU t c) (shootingFlow T hT T c) := by
      simpa only [dist_eq_norm,Pi.sub_apply,Real.norm_eq_abs] using
        norm_le_pi_norm (shootingFlow U hU t c-shootingFlow T hT T c) i
    have ha := abs_add_le (shootingFlow U hU t c i-shootingFlow T hT T c i)
      (shootingFlow T hT T c i)
    rw [sub_add_cancel] at ha
    have hmax : t≤T+1/16000 := ht.2
    have hinner := hc T (right_mem_Icc.mpr hT) i hi
    change |shootingFlow U hU t c i|≤_
    linarith

lemma actualShootingMap_extended_center_eq {T : ℝ} (hT : 0≤T) {p : Fin 3 → ℝ}
    (hp : p 2=T) :
    actualShootingMap (shootingExtendedHorizon T) (shootingExtendedHorizon_nonneg hT) p=
      actualShootingMap T hT p := by
  unfold actualShootingMap
  rw [hp,shootingFlow_horizon_compatibility hT (shootingExtendedHorizon_nonneg hT)
    (show T≤shootingExtendedHorizon T by unfold shootingExtendedHorizon; linarith)
    (shootingInitial p) (right_mem_Icc.mpr hT)]

/-- Executable grid checks discharge the trajectory-region hypotheses for
the genuine three-parameter derivative on a whole open ball. -/
theorem checked_grid_actualShootingMap_differentiable_extended
    {S N : ℕ} (hS : 0<S) (hN : 0<N) {h : ℚ} (hh : 0≤h) (hhmax : h≤1/100)
    {b : BallVector} (hcheck : (computeBallGrid S h b N).checks=true)
    {p₀ : Fin 3 → ℝ} (hc0 : ∀ i, (b i).Contains (shootingInitial p₀ i))
    (hcenter : p₀ 2=(N:ℝ)*(h:ℝ)) (hpos : 0<(N:ℝ)*(h:ℝ)) :
    let T : ℝ := (N:ℝ)*(h:ℝ)
    let U := shootingExtendedHorizon T
    let hU : 0≤U := shootingExtendedHorizon_nonneg hpos.le
    ∀ p∈Metric.ball p₀ (shootingParameterRadius T),
      HasFDerivAt (actualShootingMap U hU) (actualShootingDifferential U hU p) p := by
  intro T U hU p hp
  exact actualShootingMap_hasFDerivAt_extended hpos hcenter
    (shootingFlow_inner_of_checked_grid hS hN hh hhmax hcheck hc0) hp

end
end CentroidEscape

#print axioms CentroidEscape.actualShootingMap_hasFDerivAt_extended
#print axioms CentroidEscape.actualShootingMap_fderiv_variation_extended

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
  logInfo m!"Shooting-domain audit passed for {checked} declarations."
