import CentroidEscape.VectorPolynomial
import CentroidEscape.ResidualFlow

/-!
# Actual unclipped ODE solutions from the finite Taylor polynomial

The initial margin is a numerical check on the center only. Existence,
the differential equation, and inactivity of clipping on the whole step
are conclusions. Concrete interval iteration is still a separate check.
-/
namespace CentroidEscape
noncomputable section
open Set Real
set_option backward.isDefEq.respectTransparency false

lemma canonicalTaylorPolynomial_zero (a : WeightedState) :
    canonicalTaylorPolynomial a 0 = a := by
  unfold canonicalTaylorPolynomial
  suffices hsum : (∑ n ∈ Finset.range 161, (0:ℝ)^n • canonicalTaylorCoeff a n) = 0 by
    rw [hsum, add_zero]
  apply Finset.sum_eq_zero
  intro n _
  by_cases hn : n = 0
  · subst n; simp [canonicalTaylorCoeff_zero]
  · simp [zero_pow hn]

lemma polynomialResidual_lt_small : polynomialResidual < (1/1000000 : ℚ) := by
  decide +kernel

theorem exists_canonical_step {a : WeightedState}
    (ha : ∀ i : Fin 7, i ≠ 6 → |a i| ≤ tubeRadius i-24/1000)
    {h : ℝ} (hh : 0 ≤ h) (hhmax : h ≤ 1/100) :
    ∃ z : ℝ → WeightedState, z 0 = a ∧
      (∀ t ∈ Icc 0 h, HasDerivAt z (weightedField (z t)) t) ∧
      (∀ t ∈ Icc 0 h, z t ∈ weightedTube) ∧
      (∀ t ∈ Icc 0 h, dist (z t) (canonicalTaylorPolynomial a t) ≤
        (polynomialResidual:ℝ)*t*exp (8*t)) := by
  have ha23 : ∀ i : Fin 7, i ≠ 6 → |a i| ≤ tubeRadius i-23/1000 := by
    intro i hi
    linarith [ha i hi]
  have hat : a ∈ weightedTube := by
    intro i hi
    linarith [ha i hi]
  have hε : (0:ℝ) ≤ (polynomialResidual:ℝ) := by
    exact_mod_cast polynomialResidual_positive.le
  obtain ⟨z, hz0, hz⟩ := exists_ode_on_finite_interval clippedField 8 2 a h hh
    clippedField_lipschitz clippedField_bound
  have herr : ∀ t ∈ Icc 0 h, dist (z t) (canonicalTaylorPolynomial a t) ≤
      (polynomialResidual:ℝ)*t*exp (8*t) := by
    intro t ht
    have hs := approximate_step_error clippedField 8 0 t (polynomialResidual:ℝ)
      ht.1 hε z (canonicalTaylorPolynomial a) (canonicalTaylorDerivative a)
      clippedField_lipschitz
      (fun s hs => (hz s ⟨hs.1, hs.2.trans ht.2⟩).continuousAt.continuousWithinAt)
      (fun s hs => hz s ⟨hs.1, hs.2.le.trans ht.2⟩)
      (fun s _ => (canonicalTaylorPolynomial_hasDerivAt a s).continuousAt.continuousWithinAt)
      (fun s _ => canonicalTaylorPolynomial_hasDerivAt a s)
      (by
        intro s hs
        rw [dist_eq_norm]
        rw [← (canonicalTaylorPolynomial_hasDerivAt a s).deriv]
        exact canonicalTaylorPolynomial_clipped_residual_uniform ha23 hs.1
          (hs.2.le.trans (ht.2.trans hhmax)))
    simpa only [hz0, canonicalTaylorPolynomial_zero, dist_self, zero_mul,
      zero_add, sub_zero, NNReal.coe_ofNat] using hs
  have hmem : ∀ t ∈ Icc 0 h, z t ∈ weightedTube := by
    intro t ht
    have hsmall : (polynomialResidual:ℝ) < 1/1000000 := by
      have hc : (polynomialResidual:ℝ) < ((1/1000000:ℚ):ℝ) :=
        Rat.cast_lt.mpr polynomialResidual_lt_small
      norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hc
      exact hc
    have hexp : exp (8*t) < 3 := by
      have harg : 8*t ≤ 1 := by linarith [ht.2]
      have he : exp 1 < 3 := by
        have hx := exp_bound' (x := (1 : ℝ)) (by norm_num) (by norm_num)
          (n := 4) (by norm_num)
        norm_num [Finset.sum_range_succ, Nat.factorial] at hx
        linarith
      exact (exp_le_exp.mpr harg).trans_lt he
    have he : dist (z t) (canonicalTaylorPolynomial a t) < 1/1000 := by
      have htmax : t ≤ 1/100 := ht.2.trans hhmax
      have hmul := mul_le_mul_of_nonneg_right hsmall.le ht.1
      have hmul' : (polynomialResidual:ℝ)*t ≤ (1/1000000)*(1/100) :=
        hmul.trans (mul_le_mul_of_nonneg_left htmax (by norm_num))
      have htotal := mul_le_mul hmul' hexp.le (exp_pos _).le (by norm_num)
      exact (herr t ht).trans_lt (by linarith)
    have hexc := canonicalTaylorPolynomial_excursion_uniform hat ht.1 (ht.2.trans hhmax)
    intro i hi
    have hdiff : |z t i-a i| < 24/1000 := by
      have hn := norm_add_le (z t-canonicalTaylorPolynomial a t) (canonicalTaylorPolynomial a t-a)
      rw [sub_add_sub_cancel] at hn
      have hcoord := norm_le_pi_norm (z t-a) i
      have hen : ‖z t-canonicalTaylorPolynomial a t‖ < 1/1000 := by
        simpa only [dist_eq_norm] using he
      simp only [Pi.sub_apply, Real.norm_eq_abs] at hcoord
      linarith
    have habs := abs_add_le (z t i-a i) (a i)
    rw [sub_add_cancel] at habs
    linarith [ha i hi]
  refine ⟨z, hz0, ?_, hmem, herr⟩
  intro t ht
  simpa only [clippedField_eq (hmem t ht)] using hz t ht

end
end CentroidEscape

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
  logInfo m!"Canonical-step audit passed: {checked} declarations; standard axioms only."
