import CentroidEscape.OrderMetricIntegration
import CentroidEscape.VariableOrderCertificate

/-!
# Composable checked order60 grids enclose actual original-field solutions

Each finite coefficient table is checked independently. Consecutive tables
reuse the preceding evaluated endpoint ball. The exact polynomial iteration
is enclosed by those balls, including all arithmetic rounding. The global
metric integration error is added once at each requested output node.
-/
namespace CentroidEscape.MetricStability
noncomputable section
open Set Real
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

def exactOrder60Grid (h : ℝ) (a : WeightedState) : ℕ → WeightedState
  | 0 => a
  | n+1 => orderTaylorPolynomial 60 (exactOrder60Grid h a n) h

theorem checkedOrder60Grid_contains {S N : ℕ} (hS : 0<S) (h : ℚ)
    (st : ℕ → FixedTaylorState)
    (hcheck : ∀ j<N, checkOrderTaylorData S 60 (st j)=true)
    (hglue : ∀ j<N, ∀ i : Fin 7,
      (st (j+1)).coefficient 0 i=(evaluateFixedTaylorOrder S 60 h (st j))[i.val])
    {a : WeightedState} (ha : ∀ i, ((st 0).coefficient 0 i).Contains S (a i)) :
    ∀ n≤N, ∀ i, ((st n).coefficient 0 i).Contains S (exactOrder60Grid (h:ℝ) a n i) := by
  intro n hn
  induction n with
  | zero => simpa only [exactOrder60Grid] using ha
  | succ n ih =>
    have hnN : n<N := Nat.lt_of_succ_le hn
    intro i
    rw [hglue n hnN i]
    exact checkedOrderTaylorEndpoint_contains hS (by omega : 60≤160) h (hcheck n hnN)
      (ih (Nat.le_of_lt hnN)) i

theorem checkedOrder60Grid_margin {S N : ℕ} (hS : 0<S) (h : ℚ)
    (st : ℕ → FixedTaylorState)
    (hcheck : ∀ j<N, checkOrderTaylorData S 60 (st j)=true)
    (hglue : ∀ j<N, ∀ i : Fin 7,
      (st (j+1)).coefficient 0 i=(evaluateFixedTaylorOrder S 60 h (st j))[i.val])
    (hmargin : ∀ j<N, checkBallCanonicalMargin
      (fun i=>((st j).coefficient 0 i).toRational S)=true)
    {a : WeightedState} (ha : ∀ i, ((st 0).coefficient 0 i).Contains S (a i)) :
    ∀ j<N, ∀ i : Fin 7, i≠6 → |exactOrder60Grid (h:ℝ) a j i|≤tubeRadius i-24/1000 := by
  intro j hj
  exact (checkBallCanonicalMargin_sound (hmargin j hj)).contains_margin
    (checkedOrder60Grid_contains hS h st hcheck hglue ha j (Nat.le_of_lt hj))

/-- The actual original-field flow, tube containment, and global node
enclosures are conclusions of finite table checks and rational margin checks. -/
theorem exists_checked_order60_metric_grid {S N : ℕ} (hS : 0<S) (hN : 0<N) (hNmax : N≤750)
    {h : ℚ} (hh : 0≤h) (hhmax : h≤1/100)
    (st : ℕ → FixedTaylorState)
    (hcheck : ∀ j<N, checkOrderTaylorData S 60 (st j)=true)
    (hglue : ∀ j<N, ∀ i : Fin 7,
      (st (j+1)).coefficient 0 i=(evaluateFixedTaylorOrder S 60 h (st j))[i.val])
    (hmargin : ∀ j<N, checkBallCanonicalMargin
      (fun i=>((st j).coefficient 0 i).toRational S)=true)
    {a : WeightedState} (ha : ∀ i, ((st 0).coefficient 0 i).Contains S (a i)) :
    ∃ z : ℝ → WeightedState, z 0=a ∧
      (∀ t∈Icc 0 ((N:ℝ)*(h:ℝ)), HasDerivAt z (weightedField (z t)) t) ∧
      (∀ t∈Icc 0 ((N:ℝ)*(h:ℝ)), z t∈innerWeightedTube) ∧
      (∀ n≤N, ∀ i : Fin 7,
        (((st n).coefficient 0 i).toRational S).inflate (1/10^43) |>.Contains
          (z ((n:ℝ)*(h:ℝ)) i)) := by
  have hh' : (0:ℝ)≤(h:ℝ) := Rat.cast_nonneg.mpr hh
  have hhmax' : (h:ℝ)≤1/100 := by
    have hm := (Rat.cast_le (K:=ℝ)).mpr hhmax
    norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hm
    exact hm
  obtain ⟨z,hz0,hz⟩ := exists_ode_on_finite_interval clippedField 8 2 a ((N:ℝ)*(h:ℝ))
    (mul_nonneg (Nat.cast_nonneg N) hh') clippedField_lipschitz clippedField_bound
  have hcenter := checkedOrder60Grid_contains hS h st hcheck hglue ha
  have hm := checkedOrder60Grid_margin hS h st hcheck hglue hmargin ha
  obtain ⟨herr,hcell⟩ := order60_metric_grid_uniform hNmax hh' hhmax'
    (exactOrder60Grid (h:ℝ) a) (fun _ _=>rfl) hm hz0 hz
  have htube : ∀ t∈Icc 0 ((N:ℝ)*(h:ℝ)), z t∈innerWeightedTube := by
    intro t ht
    obtain ⟨j,hj,r,hr,he⟩ := nonnegative_grid_covers hh' N hN ht
    rw [he]
    exact hcell j hj r hr
  refine ⟨z,hz0,?_,htube,?_⟩
  · intro t ht
    simpa only [clippedField_eq (innerWeightedTube_subset (htube t ht))] using hz t ht
  · intro n hn i
    apply RationalBall.contains_inflate_of_abs_sub_le (hcenter n hn i)
    have hc : |z ((n:ℝ)*(h:ℝ)) i-exactOrder60Grid (h:ℝ) a n i|≤
        ‖z ((n:ℝ)*(h:ℝ))-exactOrder60Grid (h:ℝ) a n‖ := by
      simpa only [Pi.sub_apply,Real.norm_eq_abs] using
        norm_le_pi_norm (z ((n:ℝ)*(h:ℝ))-exactOrder60Grid (h:ℝ) a n) i
    have he := hc.trans (herr n hn).le
    norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]
    norm_num at he
    exact he

theorem checked_order60_shootingFlow {S N : ℕ} (hS : 0<S) (hN : 0<N) (hNmax : N≤750)
    {h : ℚ} (hh : 0≤h) (hhmax : h≤1/100)
    (st : ℕ → FixedTaylorState)
    (hcheck : ∀ j<N, checkOrderTaylorData S 60 (st j)=true)
    (hglue : ∀ j<N, ∀ i : Fin 7,
      (st (j+1)).coefficient 0 i=(evaluateFixedTaylorOrder S 60 h (st j))[i.val])
    (hmargin : ∀ j<N, checkBallCanonicalMargin
      (fun i=>((st j).coefficient 0 i).toRational S)=true)
    {a : WeightedState} (ha : ∀ i, ((st 0).coefficient 0 i).Contains S (a i)) :
    (∀ t∈Icc 0 ((N:ℝ)*(h:ℝ)),
      shootingFlow ((N:ℝ)*(h:ℝ)) (mul_nonneg (Nat.cast_nonneg N) (Rat.cast_nonneg.mpr hh)) t a
        ∈innerWeightedTube) ∧
    (∀ n≤N, ∀ i : Fin 7,
      (((st n).coefficient 0 i).toRational S).inflate (1/10^43) |>.Contains
        (shootingFlow ((N:ℝ)*(h:ℝ)) (mul_nonneg (Nat.cast_nonneg N) (Rat.cast_nonneg.mpr hh))
          ((n:ℝ)*(h:ℝ)) a i)) := by
  obtain ⟨z,hz0,hz,htube,hnodes⟩ :=
    exists_checked_order60_metric_grid hS hN hNmax hh hhmax st hcheck hglue hmargin ha
  have hzc : ∀ t∈Icc 0 ((N:ℝ)*(h:ℝ)), HasDerivAt z (clippedField (z t)) t := by
    intro t ht
    simpa only [clippedField_eq (innerWeightedTube_subset (htube t ht))] using hz t ht
  have heq := shootingFlow_unique ((N:ℝ)*(h:ℝ))
    (mul_nonneg (Nat.cast_nonneg N) (Rat.cast_nonneg.mpr hh)) hz0 hzc
  constructor
  · intro t ht
    have hc := htube t ht
    rw [heq ht] at hc
    exact hc
  · intro n hn i
    have ht : (n:ℝ)*(h:ℝ)∈Icc 0 ((N:ℝ)*(h:ℝ)) := by
      constructor
      · exact mul_nonneg (Nat.cast_nonneg n) (Rat.cast_nonneg.mpr hh)
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (Rat.cast_nonneg.mpr hh)
    have hc := hnodes n hn i
    rw [heq ht] at hc
    exact hc

end
end CentroidEscape.MetricStability

#print axioms CentroidEscape.MetricStability.exists_checked_order60_metric_grid
#print axioms CentroidEscape.MetricStability.checked_order60_shootingFlow

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
  logInfo m!"Checked order60 metric grid audit passed for {checked} declarations."
