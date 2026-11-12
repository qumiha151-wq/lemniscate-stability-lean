import CentroidEscape.OrderVectorResidual
import CentroidEscape.MetricResidual

/-!
# Order60 actual integration and metric grid propagation

The grid follows the exact finite Taylor polynomial iteration. Initial
center margins are the sole tube checks; first exit is proved on each cell.
Errors are propagated in the metric, so 34 is never multiplied at each step.
-/
namespace CentroidEscape.MetricStability
noncomputable section
open Set Real
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

lemma orderTaylorPolynomial_inner {N : ℕ} (hN : N≤160) {a : WeightedState}
    (ha : ∀ i : Fin 7, i≠6 → |a i|≤tubeRadius i-24/1000)
    {t : ℝ} (ht : 0≤t) (htmax : t≤1/100) : orderTaylorPolynomial N a t∈innerWeightedTube := by
  have hat : a∈weightedTube := by intro i hi; linarith [ha i hi]
  have he := orderTaylorPolynomial_excursion_uniform hN hat ht htmax
  intro i hi
  have hc : |orderTaylorPolynomial N a t i-a i|≤‖orderTaylorPolynomial N a t-a‖ := by
    simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (orderTaylorPolynomial N a t-a) i
  have habs := abs_add_le (orderTaylorPolynomial N a t i-a i) (a i)
  rw [sub_add_cancel] at habs
  change |orderTaylorPolynomial N a t i|≤tubeRadius i-1/2000
  linarith [ha i hi]

def metricGridEnvelope (ε h : ℝ) (n : ℕ) : ℝ :=
  (n:ℝ)*ε*h*exp ((39/20)*((n:ℝ)*h))

lemma metricGridEnvelope_mono {ε h : ℝ} (hε : 0≤ε) (hh : 0≤h) :
    Monotone (metricGridEnvelope ε h) := by
  intro n m hnm
  have hnm' : (n:ℝ)≤m := by exact_mod_cast hnm
  dsimp [metricGridEnvelope]
  gcongr

lemma metricGridEnvelope_step {d ε h : ℝ} (hε : 0≤ε) (hh : 0≤h) (n : ℕ)
    (hd : d≤metricGridEnvelope ε h n) :
    gronwallBound d (39/20) ε h≤metricGridEnvelope ε h (n+1) := by
  have hbase := gronwallBound_le_residual d (39/20) ε h (by norm_num) hε
  have he : exp ((39/20)*((n:ℝ)*h))*exp ((39/20)*h)=
      exp ((39/20)*(((n:ℝ)+1)*h)) := by
    rw [← exp_add]
    congr 1
    ring
  have he2 : exp ((39/20)*h)≤exp ((39/20)*(((n:ℝ)+1)*h)) := by
    apply exp_le_exp.mpr
    nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) hh]
  calc
    _ ≤ d*exp ((39/20)*h)+ε*h*exp ((39/20)*h) := hbase
    _ ≤ metricGridEnvelope ε h n*exp ((39/20)*h)+
        ε*h*exp ((39/20)*(((n:ℝ)+1)*h)) :=
      add_le_add (mul_le_mul_of_nonneg_right hd (exp_pos _).le)
        (mul_le_mul_of_nonneg_left he2 (mul_nonneg hε hh))
    _ = metricGridEnvelope ε h (n+1) := by
      dsimp [metricGridEnvelope]
      rw [mul_assoc ((n:ℝ)*ε*h),he,Nat.cast_add,Nat.cast_one]
      ring

theorem order60_metric_grid {N : ℕ} {h : ℝ} (hh : 0≤h) (hhmax : h≤1/100)
    (p : ℕ → WeightedState) (hp : ∀ j<N, p (j+1)=orderTaylorPolynomial 60 (p j) h)
    (hmargin : ∀ j<N, ∀ i : Fin 7, i≠6 → |p j i|≤tubeRadius i-24/1000)
    {z : ℝ → WeightedState} (hz0 : z 0=p 0)
    (hz : ∀ t∈Icc 0 ((N:ℝ)*h), HasDerivAt z (clippedField (z t)) t)
    (hbudget : metricGridEnvelope (34*(finiteResidual60:ℝ)) h N<1/2000) :
    (∀ n≤N, metricNorm (z ((n:ℝ)*h)-p n)≤metricGridEnvelope (34*(finiteResidual60:ℝ)) h n) ∧
    (∀ j<N, ∀ s∈Icc 0 h, z ((j:ℝ)*h+s)∈innerWeightedTube) := by
  have hR : (0:ℝ)≤(finiteResidual60:ℝ) := Rat.cast_nonneg.mpr finiteResidual60_positive.le
  have hε : (0:ℝ)≤34*(finiteResidual60:ℝ) := by positivity
  have hlocal (j : ℕ) (hj : j<N)
      (hind : metricNorm (z ((j:ℝ)*h)-p j)≤metricGridEnvelope (34*(finiteResidual60:ℝ)) h j) :
      (∀ s∈Icc 0 h, z ((j:ℝ)*h+s)∈innerWeightedTube) ∧
      metricNorm (z (((j+1:ℕ):ℝ)*h)-p (j+1))≤
        metricGridEnvelope (34*(finiteResidual60:ℝ)) h (j+1) := by
    have hstart : p j∈weightedTube := by intro i hi; linarith [hmargin j hj i hi]
    have hstepbudget : gronwallBound
        (metricNorm (z ((j:ℝ)*h)-p j)) (39/20) (34*(finiteResidual60:ℝ)) h<1/2000 :=
      (metricGridEnvelope_step hε hh j hind).trans_lt
        (((metricGridEnvelope_mono hε hh) (Nat.succ_le_of_lt hj)).trans_lt hbudget)
    have hf : ∀ s∈Icc 0 h, HasDerivAt (fun t=>z ((j:ℝ)*h+t))
        (clippedField (z ((j:ℝ)*h+s))) s := by
      intro s hs
      have hshift : HasDerivAt (fun t:ℝ=>(j:ℝ)*h+t) 1 s := by
        simpa using (hasDerivAt_id s).const_add ((j:ℝ)*h)
      convert! (hz _ (ball_grid_cell_time hh hj hs)).scomp s hshift using 1
      simp
    have he := metric_residual_tube_of_weighted hh hR hf
      (fun s _=>(orderTaylorPolynomial_hasDerivAt 60 (p j) s).continuousAt.continuousWithinAt)
      (fun s _=>(orderTaylorPolynomial_hasDerivAt 60 (p j) s).hasDerivWithinAt)
      (fun s hs=>orderTaylorPolynomial_inner (by omega : 60≤160) (hmargin j hj)
        hs.1 (hs.2.trans hhmax))
      (fun s hs=>orderTaylor60_residual_uniform hstart hs.1 (hs.2.le.trans hhmax))
      (by simpa only [add_zero,orderTaylorPolynomial_zero] using hstepbudget)
    have hinner : ∀ s∈Icc 0 h, z ((j:ℝ)*h+s)∈innerWeightedTube := by
      intro s hs
      have he' := he.2 s hs
      simp only [add_zero,orderTaylorPolynomial_zero] at he'
      have hm := gronwallBound_mono (metricNorm_nonneg (z ((j:ℝ)*h)-p j)) hε
        (by norm_num : (0:ℝ)≤39/20) hs.2
      have hn : ‖z ((j:ℝ)*h+s)-orderTaylorPolynomial 60 (p j) s‖<1/2000 :=
        (weightedNorm_le_metricNorm _).trans_lt ((he'.trans hm).trans_lt hstepbudget)
      have hexc := orderTaylorPolynomial_excursion_uniform (by omega : 60≤160)
        hstart hs.1 (hs.2.trans hhmax)
      have hsum := norm_add_le (z ((j:ℝ)*h+s)-orderTaylorPolynomial 60 (p j) s)
        (orderTaylorPolynomial 60 (p j) s-p j)
      rw [sub_add_sub_cancel] at hsum
      intro i hi
      have hc : |z ((j:ℝ)*h+s) i-p j i|≤‖z ((j:ℝ)*h+s)-p j‖ := by
        simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (z ((j:ℝ)*h+s)-p j) i
      have habs := abs_add_le (z ((j:ℝ)*h+s) i-p j i) (p j i)
      rw [sub_add_cancel] at habs
      change |z ((j:ℝ)*h+s) i|≤tubeRadius i-1/2000
      linarith [hmargin j hj i hi]
    refine ⟨hinner,?_⟩
    have hend := (he.2 h ⟨hh,le_rfl⟩).trans
      (by simpa only [add_zero,orderTaylorPolynomial_zero] using metricGridEnvelope_step hε hh j hind)
    simpa only [hp j hj,Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hend
  have hnodes : ∀ n≤N, metricNorm (z ((n:ℝ)*h)-p n)≤metricGridEnvelope (34*(finiteResidual60:ℝ)) h n := by
    intro n hn
    induction n with
    | zero => simp [hz0,metricNorm,metricEnergy,metricGridEnvelope]
    | succ n ih =>
      have hnN : n<N := Nat.lt_of_succ_le hn
      exact (hlocal n hnN (ih (Nat.le_of_lt hnN))).2
  exact ⟨hnodes,fun j hj=>(hlocal j hj (hnodes j (Nat.le_of_lt hj))).1⟩

lemma finiteResidual60_unpadded_budget :
    (750:ℚ)*34*finiteResidual60*(1/100)*4000000<1/10^43 := by decide +kernel

theorem metricGridEnvelope60_budget {N : ℕ} (hN : N≤750) {h : ℝ}
    (hh : 0≤h) (hhmax : h≤1/100) :
    metricGridEnvelope (34*(finiteResidual60:ℝ)) h N<1/(10:ℝ)^43 := by
  have hR : (0:ℝ)≤(finiteResidual60:ℝ) := Rat.cast_nonneg.mpr finiteResidual60_positive.le
  have hN' : (N:ℝ)≤750 := by exact_mod_cast hN
  have htime : (N:ℝ)*h≤15/2 := by nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) N) hh]
  have hexp := (metric_exp_budget htime).le
  have he : metricGridEnvelope (34*(finiteResidual60:ℝ)) h N≤
      750*34*(finiteResidual60:ℝ)*(1/100)*4000000 := by
    dsimp [metricGridEnvelope]
    calc
      _ ≤ 750*(34*(finiteResidual60:ℝ))*(1/100)*4000000 := by gcongr
      _ = _ := by ring
  have hb := (Rat.cast_lt (K:=ℝ)).mpr finiteResidual60_unpadded_budget
  norm_num only [Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_one,Rat.cast_ofNat] at hb
  exact he.trans_lt (by convert hb using 1 <;> norm_num)

theorem order60_metric_grid_uniform {N : ℕ} (hN : N≤750) {h : ℝ}
    (hh : 0≤h) (hhmax : h≤1/100)
    (p : ℕ → WeightedState) (hp : ∀ j<N, p (j+1)=orderTaylorPolynomial 60 (p j) h)
    (hmargin : ∀ j<N, ∀ i : Fin 7, i≠6 → |p j i|≤tubeRadius i-24/1000)
    {z : ℝ → WeightedState} (hz0 : z 0=p 0)
    (hz : ∀ t∈Icc 0 ((N:ℝ)*h), HasDerivAt z (clippedField (z t)) t) :
    (∀ n≤N, ‖z ((n:ℝ)*h)-p n‖<1/(10:ℝ)^43) ∧
    (∀ j<N, ∀ s∈Icc 0 h, z ((j:ℝ)*h+s)∈innerWeightedTube) := by
  have hb := metricGridEnvelope60_budget hN hh hhmax
  have hhbudget : metricGridEnvelope (34*(finiteResidual60:ℝ)) h N<1/2000 := by
    exact hb.trans (by norm_num)
  obtain ⟨he,htube⟩ := order60_metric_grid hh hhmax p hp hmargin hz0 hz hhbudget
  refine ⟨?_,htube⟩
  intro n hn
  exact (weightedNorm_le_metricNorm _).trans_lt
    ((he n hn).trans_lt (metricGridEnvelope60_budget (hn.trans hN) hh hhmax))

end
end CentroidEscape.MetricStability

#print axioms CentroidEscape.MetricStability.order60_metric_grid_uniform

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
  logInfo m!"Order60 metric integration audit passed for {checked} declarations."
