import CentroidEscape.BallGrid

/-!
# Uniform interior margin for a genuinely checked trajectory

The certified .024 input margin and <.023 polynomial excursion leave a
uniform .0005 margin even after the actual analytic local error. Thus the
clipped field is identically the original polynomial field on a common
radius neighborhood of every certified trajectory state. This supplies
the local smoothness interface needed for actual parameter variations;
global smoothness of the clipped field is neither asserted nor assumed.
-/
namespace CentroidEscape
noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

def innerWeightedTube : Set WeightedState :=
  {a | ∀ i : Fin 7, i ≠ 6 → |a i| ≤ tubeRadius i-1/2000}

lemma canonicalStepAllowance_lt_inner_margin :
    (canonicalStepAllowance:ℝ) < 1/2000 := by
  have he : (polynomialResidual:ℝ) < ((1/1000000:ℚ):ℝ) :=
    Rat.cast_lt.mpr polynomialResidual_lt_small
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at he
  simp only [canonicalStepAllowance, Rat.cast_div, Rat.cast_ofNat]
  linarith

/-- A true clipped trajectory has a uniform strict interior margin. The
margin is a conclusion from its initial state and the actual ODE. -/
theorem clipped_trajectory_inner_tube {h : ℝ} (hh : 0 ≤ h) (hhmax : h ≤ 1/100)
    {w : ℝ → WeightedState}
    (ha : ∀ i : Fin 7, i ≠ 6 → |w 0 i| ≤ tubeRadius i-24/1000)
    (hw : ∀ t ∈ Icc 0 h, HasDerivAt w (clippedField (w t)) t) :
    ∀ t ∈ Icc 0 h, w t ∈ innerWeightedTube := by
  have haTube : w 0 ∈ weightedTube := by intro i hi; linarith [ha i hi]
  obtain ⟨z,hz0,hz,htube,herr⟩ := exists_canonical_step ha hh hhmax
  have hzc : ∀ t ∈ Icc 0 h, HasDerivAt z (clippedField (z t)) t := by
    intro t ht
    simpa only [clippedField_eq (htube t ht)] using hz t ht
  have heq := clipped_step_unique hw hzc hz0.symm
  intro t ht
  rw [heq ht]
  have he : ‖z t-canonicalTaylorPolynomial (w 0) t‖ < 1/2000 := by
    rw [← dist_eq_norm]
    exact ((herr t ht).trans (canonical_error_le_allowance ht.1
      (ht.2.trans hhmax))).trans_lt canonicalStepAllowance_lt_inner_margin
  have hp := canonicalTaylorPolynomial_excursion_uniform haTube ht.1 (ht.2.trans hhmax)
  have hn := norm_add_le (z t-canonicalTaylorPolynomial (w 0) t)
    (canonicalTaylorPolynomial (w 0) t-w 0)
  rw [sub_add_sub_cancel] at hn
  intro i hi
  have hd : |z t i-w 0 i| ≤ ‖z t-w 0‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (z t-w 0) i
  have habs := abs_add_le (z t i-w 0 i) (w 0 i)
  rw [sub_add_cancel] at habs
  linarith [ha i hi]

lemma innerWeightedTube_subset : innerWeightedTube ⊆ weightedTube := by
  intro a ha i hi
  linarith [ha i hi]

/-- On the fixed radius .0005 neighborhood of any certified state the
clipped and original polynomial fields agree identically. -/
theorem clippedField_eq_on_inner_ball {a : WeightedState} (ha : a ∈ innerWeightedTube)
    {b : WeightedState} (hb : b ∈ Metric.ball a (1/2000)) :
    clippedField b = weightedField b := by
  apply clippedField_eq
  intro i hi
  have hd : |b i-a i| ≤ dist b a := by
    simpa only [dist_eq_norm, Pi.sub_apply, Real.norm_eq_abs] using
      norm_le_pi_norm (b-a) i
  have hdist : dist b a < 1/2000 := hb
  have habs := abs_add_le (b i-a i) (a i)
  rw [sub_add_cancel] at habs
  linarith [ha i hi]

theorem clippedField_eventually_eq_of_inner {a : WeightedState} (ha : a ∈ innerWeightedTube) :
    clippedField =ᶠ[𝓝 a] weightedField := by
  filter_upwards [Metric.ball_mem_nhds a (by norm_num : (0:ℝ)<1/2000)] with b hb
  exact clippedField_eq_on_inner_ball ha hb

/-- The whole actual trajectory certified by finite ball checks has the
same positive interior margin, independent of the grid index. -/
theorem checked_ball_grid_inner {S N : ℕ} (hS : 0<S) (hN : 0<N)
    {h : ℚ} (hh : 0 ≤ h) (hhmax : h ≤ 1/100) {b : BallVector}
    (hc : (computeBallGrid S h b N).checks = true)
    {z : ℝ → WeightedState} (hz0 : ∀ i, (b i).Contains (z 0 i))
    (hz : ∀ t ∈ Icc 0 ((N:ℝ)*(h:ℝ)), HasDerivAt z (clippedField (z t)) t) :
    ∀ t ∈ Icc 0 ((N:ℝ)*(h:ℝ)), z t ∈ innerWeightedTube := by
  have hh' : (0:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hhmax' : (h:ℝ) ≤ 1/100 := by
    have hm : (h:ℝ) ≤ ((1/100:ℚ):ℝ) := Rat.cast_le.mpr hhmax
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hm
    exact hm
  have hnodes := (checked_ball_grid_trajectory hS hh hhmax hc hz0 hz).1
  have hchecks := computeBallGrid_checks hc
  intro t ht
  obtain ⟨j,hj,r,hr,he⟩ := nonnegative_grid_covers hh' N hN ht
  have hw : ∀ r ∈ Icc 0 (h:ℝ), HasDerivAt
      (fun s => z ((j:ℝ)*(h:ℝ)+s))
      (clippedField (z ((j:ℝ)*(h:ℝ)+r))) r := by
    intro r hr
    have hs : HasDerivAt (fun s : ℝ => (j:ℝ)*(h:ℝ)+s) 1 r := by
      simpa using ((hasDerivAt_id r).const_add ((j:ℝ)*(h:ℝ)))
    convert! (hz _ (ball_grid_cell_time hh' hj hr)).scomp r hs using 1
    simp
  have hstart : ∀ i, ((computeBallGrid S h b j).ball i).Contains
      ((fun s => z ((j:ℝ)*(h:ℝ)+s)) 0 i) := by
    simpa only [add_zero] using hnodes j (by omega)
  have hmargin := (checkBallCanonicalMargin_sound (hchecks j hj)).contains_margin hstart
  simpa only [he] using clipped_trajectory_inner_tube hh' hhmax' hmargin hw r hr

theorem exists_checked_ball_grid_interior {S N : ℕ} (hS : 0<S) (hN : 0<N)
    {h : ℚ} (hh : 0 ≤ h) (hhmax : h ≤ 1/100) {b : BallVector}
    (hc : (computeBallGrid S h b N).checks = true) {a : WeightedState}
    (ha : ∀ i, (b i).Contains (a i)) :
    ∃ z : ℝ → WeightedState, z 0=a ∧
      (∀ t ∈ Icc 0 ((N:ℝ)*(h:ℝ)), HasDerivAt z (weightedField (z t)) t) ∧
      (∀ t ∈ Icc 0 ((N:ℝ)*(h:ℝ)), z t ∈ innerWeightedTube) ∧
      (∀ n≤N, ∀ i, ((computeBallGrid S h b n).ball i).Contains
        (z ((n:ℝ)*(h:ℝ)) i)) := by
  obtain ⟨z,hz0,hz,htube,hnodes⟩ := exists_checked_ball_grid hS hN hh hhmax hc ha
  have hzc : ∀ t ∈ Icc 0 ((N:ℝ)*(h:ℝ)), HasDerivAt z (clippedField (z t)) t := by
    intro t ht
    simpa only [clippedField_eq (htube t ht)] using hz t ht
  exact ⟨z,hz0,hz,checked_ball_grid_inner hS hN hh hhmax hc
    (by simpa only [hz0] using ha) hzc,hnodes⟩

end
end CentroidEscape

#print axioms CentroidEscape.clippedField_eventually_eq_of_inner
#print axioms CentroidEscape.exists_checked_ball_grid_interior

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
  logInfo m!"Ball-interior audit passed for {checked} declarations."
