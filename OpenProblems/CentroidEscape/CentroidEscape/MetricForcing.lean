import CentroidEscape.MetricFlow

/-!
# Exponentially growing forcing in the certified metric

Keeping the time dependence of the forcing avoids an extra exponential
factor in the midpoint defect of the actual solution map.
-/
namespace CentroidEscape.MetricStability
noncomputable section
open Set Real
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

theorem sqrt_energy_exp_forcing {W W' : ℝ → ℝ} {T K C : ℝ}
    (hK : 0<K) (hC : 0≤C)
    (hc : ContinuousOn W (Icc 0 T)) (hzero : W 0=0)
    (hn : ∀ t∈Icc 0 T, 0≤W t)
    (hd : ∀ t∈Ico 0 T, HasDerivWithinAt W (W' t) (Ici t) t)
    (hb : ∀ t∈Ico 0 T,
      W' t≤2*K*W t+2*C*exp (2*K*t)*sqrt (W t)) :
    ∀ t∈Icc 0 T, sqrt (W t)≤(C/K)*exp (2*K*t) := by
  have H (ε : ℝ) (hε : 0<ε) : ∀ t∈Icc 0 T,
      sqrt (W t+ε^2)-(C/K)*exp (2*K*t)≤ε*exp (K*t) := by
    have hdε : ∀ t∈Ico 0 T,
        HasDerivWithinAt (fun s=>sqrt (W s+ε^2)-(C/K)*exp (2*K*s))
          (W' t/(2*sqrt (W t+ε^2))-(C/K)*(exp (2*K*t)*(2*K))) (Ici t) t := by
      intro t ht
      apply (((hd t ht).add_const (ε^2)).sqrt
        (by nlinarith [hn t (Ico_subset_Icc_self ht)])).sub
      simpa only [id_eq,mul_one] using
        ((((hasDerivAt_id t).const_mul (2*K)).exp).const_mul (C/K)).hasDerivWithinAt (s:=Ici t)
    have hh := le_gronwallBound_of_liminf_deriv_right_le
      (δ:=ε) (K:=K) (ε:=0)
      ((Real.continuous_sqrt.comp_continuousOn (hc.add_const (ε^2))).sub
        ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn))
      (fun t ht r hr=>(hdε t ht).liminf_right_slope_le hr)
      (show sqrt (W 0+ε^2)-(C/K)*exp (2*K*0)≤ε by
        simp only [hzero,zero_add,Real.sqrt_sq_eq_abs,abs_of_pos hε,mul_zero,exp_zero,mul_one]
        exact sub_le_self _ (div_nonneg hC hK.le))
      (fun t ht=>by
        have hn' := hn t (Ico_subset_Icc_self ht)
        have hp : 0<W t+ε^2 := by nlinarith
        have hspos := Real.sqrt_pos.mpr hp
        have hs := Real.sqrt_le_sqrt (show W t≤W t+ε^2 by nlinarith)
        have hsq := sq_sqrt hp.le
        have hsub : W' t/(2*sqrt (W t+ε^2))≤K*sqrt (W t+ε^2)+C*exp (2*K*t) := by
          apply (div_le_iff₀ (by positivity : 0<2*sqrt (W t+ε^2))).mpr
          nlinarith [hb t ht,mul_nonneg hK.le (sq_nonneg ε),
            mul_nonneg (mul_nonneg hC (exp_pos (2*K*t)).le) (sub_nonneg.mpr hs)]
        have he : (C/K)*(exp (2*K*t)*(2*K))=
            K*((C/K)*exp (2*K*t))+C*exp (2*K*t) := by
          field_simp
          ring
        change W' t/(2*sqrt (W t+ε^2))-(C/K)*(exp (2*K*t)*(2*K))≤
          K*(sqrt (W t+ε^2)-(C/K)*exp (2*K*t))+0
        rw [he]
        linarith)
    simpa only [gronwallBound_ε0,sub_zero,Function.comp_apply,Pi.sub_apply,Pi.mul_apply,id_eq] using hh
  intro t ht
  apply le_of_forall_pos_le_add
  intro η hη
  have he : 0<exp (K*t) := exp_pos _
  have hε : 0<η/exp (K*t) := div_pos hη he
  have heq : (η/exp (K*t))*exp (K*t)=η := div_mul_cancel₀ _ he.ne'
  have hh := H (η/exp (K*t)) hε t ht
  rw [heq] at hh
  have hs := Real.sqrt_le_sqrt
    (show W t≤W t+(η/exp (K*t))^2 by nlinarith [sq_nonneg (η/exp (K*t))])
  linarith

/-- Actual approximate-trajectory comparison with quadratic exponential forcing. -/
theorem metric_exp_forcing_trajectories {f g f' g' : ℝ → WeightedState} {T C : ℝ}
    (hC : 0≤C)
    (hf : ContinuousOn f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (hzero : f 0=g 0)
    (hfd : ∀ t∈Ico 0 T, HasDerivWithinAt f (f' t) (Ici t) t)
    (hgd : ∀ t∈Ico 0 T, HasDerivWithinAt g (g' t) (Ici t) t)
    (hft : ∀ t∈Ico 0 T, f t∈weightedTube) (hgt : ∀ t∈Ico 0 T, g t∈weightedTube)
    (herr : ∀ t∈Ico 0 T,
      metricNorm ((f' t-g' t)-(weightedField (f t)-weightedField (g t)))≤
        C*exp (2*(39/20)*t)) :
    ∀ t∈Icc 0 T, metricNorm (f t-g t)≤(C/(39/20))*exp (2*(39/20)*t) := by
  apply sqrt_energy_exp_forcing (by norm_num : (0:ℝ)<39/20) hC
    (metricEnergy_continuousOn (hf.sub hg))
    (by simp [hzero,metricEnergy])
    (fun t _=>metricEnergy_nonneg (f t-g t))
    (fun t ht=>metricEnergy_hasDerivWithinAt ((hfd t ht).sub (hgd t ht)))
  intro t ht
  have hsplit : metricPairing (f t-g t) (f' t-g' t)=
      metricPairing (f t-g t) (weightedField (f t)-weightedField (g t))+
      metricPairing (f t-g t) ((f' t-g' t)-(weightedField (f t)-weightedField (g t))) := by
    dsimp [metricPairing]; ring
  have hmono := weightedField_oneSided (hgt t ht) (hft t ht)
  have hcs := metricPairing_le (f t-g t) ((f' t-g' t)-(weightedField (f t)-weightedField (g t)))
  have hres := mul_le_mul_of_nonneg_left (herr t ht) (metricNorm_nonneg (f t-g t))
  change 2*metricPairing (f t-g t) (f' t-g' t)≤_
  rw [hsplit]
  change _≤2*(39/20)*metricEnergy (f t-g t)+2*C*exp (2*(39/20)*t)*metricNorm (f t-g t)
  nlinarith

end
end CentroidEscape.MetricStability

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape.MetricStability).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked+1
  logInfo m!"Metric exponential-forcing audit passed: {checked} declarations; standard axioms only."
