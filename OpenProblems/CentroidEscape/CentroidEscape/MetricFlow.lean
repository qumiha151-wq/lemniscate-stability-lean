import CentroidEscape.MetricStability
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Flow comparison in the certified diagonal metric

The square-root regularization below preserves the one-sided constant K.
It never substitutes the operator norm of the full Jacobian for K.
-/
namespace CentroidEscape.MetricStability
noncomputable section
open Set Real
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

lemma gronwallBound_add_initial (d e K δ t : ℝ) :
    gronwallBound (d+e) K δ t=gronwallBound d K δ t+e*exp (K*t) := by
  unfold gronwallBound
  split_ifs with hK
  · simp [hK]
    ring
  · ring

/-- A scalar energy comparison, including times when the energy vanishes. -/
theorem sqrt_energy_comparison {W W' : ℝ → ℝ} {a b K δ : ℝ}
    (hab : a≤b) (hK : 0≤K) (hδ : 0≤δ)
    (hc : ContinuousOn W (Icc a b))
    (hn : ∀ t∈Icc a b, 0≤W t)
    (hd : ∀ t∈Ico a b, HasDerivWithinAt W (W' t) (Ici t) t)
    (hb : ∀ t∈Ico a b, W' t≤2*K*W t+2*δ*sqrt (W t)) :
    ∀ t∈Icc a b, sqrt (W t)≤gronwallBound (sqrt (W a)) K δ (t-a) := by
  have ha : 0≤W a := hn a ⟨le_rfl,hab⟩
  have H (ε : ℝ) (hε : 0<ε) : ∀ t∈Icc a b,
      sqrt (W t+ε^2)≤gronwallBound (sqrt (W a)+ε) K δ (t-a) := by
    have hdε : ∀ t∈Ico a b, HasDerivWithinAt (fun s=>sqrt (W s+ε^2))
        (W' t/(2*sqrt (W t+ε^2))) (Ici t) t := by
      intro t ht
      exact ((hd t ht).add_const (ε^2)).sqrt (by nlinarith [hn t (Ico_subset_Icc_self ht)])
    apply le_gronwallBound_of_liminf_deriv_right_le
      (Real.continuous_sqrt.comp_continuousOn (hc.add_const (ε^2)))
      (fun t ht r hr => (hdε t ht).liminf_right_slope_le hr)
    · apply (Real.sqrt_le_left (by positivity : 0≤sqrt (W a)+ε)).mpr
      nlinarith [sq_sqrt ha, sqrt_nonneg (W a)]
    · intro t ht
      have hn' := hn t (Ico_subset_Icc_self ht)
      have hp : 0<W t+ε^2 := by nlinarith
      have hspos := Real.sqrt_pos.mpr hp
      have hs := Real.sqrt_le_sqrt (show W t≤W t+ε^2 by nlinarith)
      have hsq := sq_sqrt hp.le
      have hsqK := congrArg (fun z:ℝ=>2*K*z) hsq
      apply (div_le_iff₀ (by positivity : 0<2*sqrt (W t+ε^2))).mpr
      dsimp only [Function.comp_apply]
      nlinarith [hb t ht, mul_nonneg hK (sq_nonneg ε),
        mul_nonneg hδ (sub_nonneg.mpr hs)]
  intro t ht
  apply le_of_forall_pos_le_add
  intro η hη
  have he : 0<exp (K*(t-a)) := exp_pos _
  have hε : 0<η/exp (K*(t-a)) := div_pos hη he
  have heq : (η/exp (K*(t-a)))*exp (K*(t-a))=η := div_mul_cancel₀ _ he.ne'
  calc
    sqrt (W t) ≤ sqrt (W t+(η/exp (K*(t-a)))^2) :=
      Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (η/exp (K*(t-a)))])
    _ ≤ gronwallBound (sqrt (W a)+η/exp (K*(t-a))) K δ (t-a) := H _ hε t ht
    _ = gronwallBound (sqrt (W a)) K δ (t-a)+η := by
      rw [gronwallBound_add_initial, heq]

lemma metricPairing_le (h j : WeightedState) :
    metricPairing h j≤metricNorm h*metricNorm j := by
  have hc := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (metricCoordinates h) (metricCoordinates j)
  have hs (v : WeightedState) : (∑ i : Fin 7, (metricCoordinates v i)^2)=metricEnergy v := by
    simp [Fin.sum_univ_succ,metricCoordinates,metricEnergy]
    ring
  have hp : (∑ i : Fin 7, metricCoordinates h i*metricCoordinates j i)=metricPairing h j := by
    simp [Fin.sum_univ_succ,metricCoordinates,metricPairing]
    ring
  simpa only [hs,hp,metricNorm] using hc

lemma metricEnergy_hasDerivWithinAt {f : ℝ → WeightedState} {f' : WeightedState}
    {s : Set ℝ} {t : ℝ} (hf : HasDerivWithinAt f f' s t) :
    HasDerivWithinAt (fun x=>metricEnergy (f x)) (2*metricPairing (f t) f') s t := by
  have hd (i : Fin 7) := (hasDerivWithinAt_pi.mp hf i).pow 2
  convert ((((((hd 0).add (hd 1)).add ((hd 2).const_mul 16)).add
    ((hd 3).const_mul 16)).add ((hd 4).const_mul 400)).add
    ((hd 5).const_mul (16384/25))).add (hd 6) using 1
  all_goals first | rfl | (simp [metricPairing]; ring)

lemma metricEnergy_continuousOn {f : ℝ → WeightedState} {s : Set ℝ}
    (hf : ContinuousOn f s) : ContinuousOn (fun t=>metricEnergy (f t)) s := by
  have hc (i : Fin 7) : ContinuousOn (fun t=>f t i) s := (continuous_apply i).comp_continuousOn hf
  exact ((((((hc 0).pow 2).add ((hc 1).pow 2)).add (((hc 2).pow 2).const_mul 16)).add
    (((hc 3).pow 2).const_mul 16)).add (((hc 4).pow 2).const_mul 400)).add
    (((hc 5).pow 2).const_mul (16384/25)) |>.add ((hc 6).pow 2)

/-- Compare arbitrary approximate trajectories that remain inside the true tube.
The residual assumption concerns their derivative difference, in the metric. -/
theorem metric_approx_trajectories {f g f' g' : ℝ → WeightedState} {a b δ : ℝ}
    (hab : a≤b) (hδ : 0≤δ)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfd : ∀ t∈Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (hgd : ∀ t∈Ico a b, HasDerivWithinAt g (g' t) (Ici t) t)
    (hft : ∀ t∈Ico a b, f t∈weightedTube) (hgt : ∀ t∈Ico a b, g t∈weightedTube)
    (herr : ∀ t∈Ico a b,
      metricNorm ((f' t-g' t)-(weightedField (f t)-weightedField (g t)))≤δ) :
    ∀ t∈Icc a b, metricNorm (f t-g t)≤
      gronwallBound (metricNorm (f a-g a)) (39/20) δ (t-a) := by
  apply sqrt_energy_comparison hab (by norm_num) hδ
    (metricEnergy_continuousOn (hf.sub hg))
    (fun t _ => metricEnergy_nonneg (f t-g t))
    (fun t ht => metricEnergy_hasDerivWithinAt ((hfd t ht).sub (hgd t ht)))
  intro t ht
  have hsplit : metricPairing (f t-g t) (f' t-g' t) =
      metricPairing (f t-g t) (weightedField (f t)-weightedField (g t))+
      metricPairing (f t-g t) ((f' t-g' t)-(weightedField (f t)-weightedField (g t))) := by
    dsimp [metricPairing]
    ring
  have hmono := weightedField_oneSided (hgt t ht) (hft t ht)
  have hcs := metricPairing_le (f t-g t) ((f' t-g' t)-(weightedField (f t)-weightedField (g t)))
  have hres := mul_le_mul_of_nonneg_left (herr t ht) (metricNorm_nonneg (f t-g t))
  change 2*metricPairing (f t-g t) (f' t-g' t)≤_
  rw [hsplit]
  change _≤2*(39/20)*metricEnergy (f t-g t)+2*δ*metricNorm (f t-g t)
  nlinarith

theorem metric_exact_trajectories {f g : ℝ → WeightedState} {a b : ℝ}
    (hab : a≤b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfd : ∀ t∈Ico a b, HasDerivWithinAt f (weightedField (f t)) (Ici t) t)
    (hgd : ∀ t∈Ico a b, HasDerivWithinAt g (weightedField (g t)) (Ici t) t)
    (hft : ∀ t∈Ico a b, f t∈weightedTube) (hgt : ∀ t∈Ico a b, g t∈weightedTube) :
    ∀ t∈Icc a b, metricNorm (f t-g t)≤metricNorm (f a-g a)*exp ((39/20)*(t-a)) := by
  have he := metric_approx_trajectories hab (le_refl (0:ℝ)) hf hg hfd hgd hft hgt
    (fun t _ => by simp [metricNorm,metricEnergy])
  simpa only [gronwallBound_ε0] using he

end
end CentroidEscape.MetricStability

#print axioms CentroidEscape.MetricStability.metric_approx_trajectories

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
  logInfo m!"Metric flow audit passed for {checked} declarations."
