import CentroidEscape.MetricForcing
import CentroidEscape.MetricHessian
import CentroidEscape.ShootingVariation

/-!
# Midpoint defect of the actual flow in the diagonal metric

The forcing is kept proportional to exp(2 K t) throughout comparison.
This proves a quadratic defect for actual trajectories with K=39/20.
-/
namespace CentroidEscape.MetricStability
noncomputable section
open Set Real
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

lemma metric_tube_midpoint {x y : WeightedState}
    (hx : x∈weightedTube) (hy : y∈weightedTube) :
    (1/2:ℝ) • (x+y)∈weightedTube := by
  simpa only [smul_add] using weightedTube_convex hx hy
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)+1/2=1)

theorem metric_midpoint_trajectories {f g h : ℝ → WeightedState} {T : ℝ}
    (hT : 0≤T)
    (hf : ∀ t∈Icc 0 T, HasDerivAt f (weightedField (f t)) t)
    (hg : ∀ t∈Icc 0 T, HasDerivAt g (weightedField (g t)) t)
    (hh : ∀ t∈Icc 0 T, HasDerivAt h (weightedField (h t)) t)
    (hft : ∀ t∈Icc 0 T, f t∈weightedTube)
    (hgt : ∀ t∈Icc 0 T, g t∈weightedTube)
    (hht : ∀ t∈Icc 0 T, h t∈weightedTube)
    (hzero : (1/2:ℝ) • (f 0+g 0)=h 0) :
    ∀ t∈Icc 0 T,
      metricNorm ((1/2:ℝ) • (f t+g t)-h t)≤
        (5/26)*exp (2*(39/20)*t)*(metricNorm (f 0-g 0))^2 := by
  have hfc : ContinuousOn f (Icc 0 T) := fun t ht=>(hf t ht).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Icc 0 T) := fun t ht=>(hg t ht).continuousAt.continuousWithinAt
  have hhc : ContinuousOn h (Icc 0 T) := fun t ht=>(hh t ht).continuousAt.continuousWithinAt
  have hdist := metric_exact_trajectories hT hfc hgc
    (fun t ht=>(hf t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht=>(hg t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht=>hft t (Ico_subset_Icc_self ht))
    (fun t ht=>hgt t (Ico_subset_Icc_self ht))
  have hres : ∀ t∈Ico 0 T,
      metricNorm (((1/2:ℝ) • (weightedField (f t)+weightedField (g t))-weightedField (h t))-
        (weightedField ((1/2:ℝ) • (f t+g t))-weightedField (h t)))≤
        ((3/8)*(metricNorm (f 0-g 0))^2)*exp (2*(39/20)*t) := by
    intro t ht
    have ht' := Ico_subset_Icc_self ht
    have he : ((1/2:ℝ) • (weightedField (f t)+weightedField (g t))-weightedField (h t))-
        (weightedField ((1/2:ℝ) • (f t+g t))-weightedField (h t))=
        (1/2:ℝ) • (weightedField (f t)+weightedField (g t))-
          weightedField ((1/2:ℝ) • (f t+g t)) := by abel
    rw [he]
    have hb := weightedField_midpoint_metric_bound (hft t ht') (hgt t ht')
    have hd : metricNorm (f t-g t)≤metricNorm (f 0-g 0)*exp ((39/20)*t) := by
      simpa only [sub_zero] using hdist t ht'
    have hds := (sq_le_sq₀ (metricNorm_nonneg (f t-g t))
      (mul_nonneg (metricNorm_nonneg (f 0-g 0)) (exp_pos _).le)).mpr hd
    have hexp : exp (2*(39/20)*t)=(exp ((39/20)*t))^2 := by
      rw [pow_two,← exp_add]
      congr 1
      ring
    rw [hexp]
    nlinarith
  have hcmp := metric_exp_forcing_trajectories
    (C:=(3/8)*(metricNorm (f 0-g 0))^2) (by positivity)
    ((hfc.add hgc).const_smul (1/2:ℝ)) hhc hzero
    (fun t ht=>((hf t (Ico_subset_Icc_self ht)).add
      (hg t (Ico_subset_Icc_self ht))).hasDerivWithinAt.const_smul (1/2:ℝ))
    (fun t ht=>(hh t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht=>metric_tube_midpoint (hft t (Ico_subset_Icc_self ht))
      (hgt t (Ico_subset_Icc_self ht)))
    (fun t ht=>hht t (Ico_subset_Icc_self ht)) hres
  intro t ht
  have hb := hcmp t ht
  convert! hb using 1
  ring

/-- The midpoint estimate for the actual finite-horizon shooting solution. -/
theorem shootingFlow_metric_midpoint (T : ℝ) (hT : 0≤T) (a b : WeightedState)
    (ha : ∀ t∈Icc 0 T, shootingFlow T hT t a∈weightedTube)
    (hb : ∀ t∈Icc 0 T, shootingFlow T hT t b∈weightedTube)
    (hm : ∀ t∈Icc 0 T, shootingFlow T hT t ((1/2:ℝ) • (a+b))∈weightedTube) :
    ∀ t∈Icc 0 T,
      metricNorm ((1/2:ℝ) • (shootingFlow T hT t a+shootingFlow T hT t b)-
        shootingFlow T hT t ((1/2:ℝ) • (a+b)))≤
        (5/26)*exp (2*(39/20)*t)*(metricNorm (a-b))^2 := by
  have hd (u : WeightedState) (hu : ∀ t∈Icc 0 T, shootingFlow T hT t u∈weightedTube)
      (t : ℝ) (ht : t∈Icc 0 T) :
      HasDerivAt (fun s=>shootingFlow T hT s u) (weightedField (shootingFlow T hT t u)) t := by
    have he := shootingFlow_derivative T hT u ht
    rwa [clippedField_eq (hu t ht)] at he
  have he := metric_midpoint_trajectories hT (hd a ha) (hd b hb)
    (hd ((1/2:ℝ) • (a+b)) hm) ha hb hm (by simp only [shootingFlow_zero])
  simpa only [shootingFlow_zero] using he

end
end CentroidEscape.MetricStability

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
  logInfo m!"Metric midpoint-flow audit passed: {checked} declarations; standard axioms only."
