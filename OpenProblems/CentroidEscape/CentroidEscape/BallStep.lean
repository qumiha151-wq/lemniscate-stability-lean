import CentroidEscape.CanonicalStep
import CentroidEscape.BallTaylor

/-!
# Rational endpoint enclosures of actual unclipped ODE steps

The ball algorithm encloses the canonical polynomial. A fixed rational
allowance then encloses a genuine original-field trajectory. The center's
margin is checked only initially; whole-step inactivity of clipping is a
conclusion of CanonicalStep. No grid-wide error estimate is inferred here
from repeatedly wrapping balls.
-/
namespace CentroidEscape
open Set Real
set_option backward.isDefEq.respectTransparency false

/-- One local analytic error allowance for every step of length at most .01.
It equals (25/23)*(1/100)*polynomialResidual. -/
def canonicalStepAllowance : ℚ := polynomialResidual / 92

lemma canonicalStepAllowance_nonneg : 0 ≤ canonicalStepAllowance :=
  div_nonneg polynomialResidual_positive.le (by norm_num)

lemma canonical_exp_bound {t : ℝ} (ht : t ≤ 1/100) : exp (8*t) ≤ 25/23 := by
  have he := mul_le_mul_of_nonneg_right (add_one_le_exp (-(8*t))) (exp_pos (8*t)).le
  rw [← exp_add, neg_add_cancel, exp_zero] at he
  have hf : (23/25 : ℝ) ≤ -(8*t)+1 := by linarith
  have hb := mul_le_mul_of_nonneg_right hf (exp_pos (8*t)).le
  linarith

lemma canonical_error_le_allowance {t : ℝ} (_ht : 0 ≤ t) (htmax : t ≤ 1/100) :
    (polynomialResidual:ℝ)*t*exp (8*t) ≤ (canonicalStepAllowance:ℝ) := by
  have hε : (0:ℝ) ≤ (polynomialResidual:ℝ) := by
    exact_mod_cast polynomialResidual_positive.le
  calc
    (polynomialResidual:ℝ)*t*exp (8*t) ≤ (polynomialResidual:ℝ)*(1/100)*(25/23) :=
      mul_le_mul (mul_le_mul_of_nonneg_left htmax hε) (canonical_exp_bound htmax)
        (exp_pos _).le (mul_nonneg hε (by norm_num))
    _ = (canonicalStepAllowance:ℝ) := by
      simp only [canonicalStepAllowance, Rat.cast_div, Rat.cast_ofNat]
      ring

/-- This is only the analytic truncation contribution to the published
750-step budget. It does not include interval-width wrapping or rounding. -/
lemma canonicalStepAllowance_global_budget :
    (750:ℚ)*(11/4)^60*canonicalStepAllowance < 1/10^118 := by
  convert polynomialResidual_budget using 1
  unfold canonicalStepAllowance
  ring

namespace RationalBall

def inflate (b : RationalBall) (d : ℚ) : RationalBall := ⟨b.center,b.radius+d⟩

lemma contains_inflate_of_abs_sub_le {b : RationalBall} {d : ℚ} {x y : ℝ}
    (hy : b.Contains y) (hxy : |x-y| ≤ (d:ℝ)) : (inflate b d).Contains x := by
  unfold Contains inflate at *
  simp only [Rat.cast_add]
  calc
    |x-(b.center:ℝ)| = |(x-y)+(y-(b.center:ℝ))| := by rw [sub_add_sub_cancel]
    _ ≤ |x-y|+|y-(b.center:ℝ)| := abs_add_le _ _
    _ ≤ (d:ℝ)+(b.radius:ℝ) := add_le_add hxy hy
    _ = (b.radius:ℝ)+(d:ℝ) := add_comm _ _

end RationalBall

/-- Executable outward-rounded polynomial endpoint plus the fixed analytic
error allowance. Each component remains an exact rational ball. -/
def ballCanonicalStep (S : ℕ) (h : ℚ) (b : BallVector) : Vector RationalBall 7 :=
  (ballTaylorEndpoint S h b).map (fun c => c.inflate canonicalStepAllowance)

def rationalTubeRadius : Fin 7 → ℚ := ![8/5,12/5,11/40,11/40,7/32,3/32,0]

lemma rationalTubeRadius_cast (i : Fin 7) : (rationalTubeRadius i:ℝ) = tubeRadius i := by
  fin_cases i <;> norm_num [rationalTubeRadius, tubeRadius]

/-- A finite exact-rational check ensuring the entire input ball has the
initial margin required by the true-step theorem. Coordinate 6 is unbounded. -/
def BallCanonicalMargin (b : BallVector) : Prop :=
  ∀ i : Fin 7, i ≠ 6 → |(b i).center|+(b i).radius ≤ rationalTubeRadius i-24/1000

instance (b : BallVector) : Decidable (BallCanonicalMargin b) := by
  unfold BallCanonicalMargin
  infer_instance

def checkBallCanonicalMargin (b : BallVector) : Bool := decide (BallCanonicalMargin b)

lemma checkBallCanonicalMargin_sound {b : BallVector} (hb : checkBallCanonicalMargin b = true) :
    BallCanonicalMargin b := of_decide_eq_true hb

lemma BallCanonicalMargin.contains_margin {b : BallVector} (hb : BallCanonicalMargin b)
    {a : WeightedState} (ha : ∀ i, (b i).Contains (a i)) :
    ∀ i : Fin 7, i ≠ 6 → |a i| ≤ tubeRadius i-24/1000 := by
  intro i hi
  have hm : (((|(b i).center|+(b i).radius):ℚ):ℝ) ≤
      (((rationalTubeRadius i-24/1000):ℚ):ℝ) := Rat.cast_le.mpr (hb i hi)
  norm_num only [Rat.cast_add, Rat.cast_abs, Rat.cast_sub, Rat.cast_div,
    Rat.cast_ofNat, rationalTubeRadius_cast] at hm
  have ht := abs_add_le (a i-((b i).center:ℝ)) ((b i).center:ℝ)
  rw [sub_add_cancel] at ht
  have hc := ha i
  change |a i-((b i).center:ℝ)| ≤ ((b i).radius:ℝ) at hc
  linarith

theorem exists_ballCanonicalStep {S : ℕ} (hS : 0<S) {h : ℚ}
    (hh : 0 ≤ h) (hhmax : h ≤ 1/100) {b : BallVector} {a : WeightedState}
    (hcontain : ∀ i, (b i).Contains (a i))
    (ha : ∀ i : Fin 7, i ≠ 6 → |a i| ≤ tubeRadius i-24/1000) :
    ∃ z : ℝ → WeightedState, z 0 = a ∧
      (∀ t ∈ Icc 0 (h:ℝ), HasDerivAt z (weightedField (z t)) t) ∧
      (∀ t ∈ Icc 0 (h:ℝ), z t ∈ weightedTube) ∧
      (∀ i : Fin 7, (ballCanonicalStep S h b)[i.val].Contains (z (h:ℝ) i)) := by
  have hh' : (0:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hhmax' : (h:ℝ) ≤ 1/100 := by
    have hc : (h:ℝ) ≤ ((1/100:ℚ):ℝ) := Rat.cast_le.mpr hhmax
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hc
    exact hc
  obtain ⟨z, hz0, hz, htube, herr⟩ := exists_canonical_step ha hh' hhmax'
  refine ⟨z, hz0, hz, htube, fun i => ?_⟩
  simp only [ballCanonicalStep, Vector.getElem_map]
  apply RationalBall.contains_inflate_of_abs_sub_le
    (ballTaylorEndpoint_contains hS h hcontain i)
  have hc : |z (h:ℝ) i-canonicalTaylorPolynomial a (h:ℝ) i| ≤
      dist (z (h:ℝ)) (canonicalTaylorPolynomial a (h:ℝ)) := by
    simpa only [dist_eq_norm, Pi.sub_apply, Real.norm_eq_abs] using
      norm_le_pi_norm (z (h:ℝ)-canonicalTaylorPolynomial a (h:ℝ)) i
  exact hc.trans ((herr (h:ℝ) ⟨hh',le_rfl⟩).trans (canonical_error_le_allowance hh' hhmax'))

lemma clipped_step_unique {f g : ℝ → WeightedState} {h : ℝ}
    (hf : ∀ t ∈ Icc 0 h, HasDerivAt f (clippedField (f t)) t)
    (hg : ∀ t ∈ Icc 0 h, HasDerivAt g (clippedField (g t)) t)
    (h0 : f 0 = g 0) : Set.EqOn f g (Icc 0 h) := by
  intro t ht
  have he := approximate_step_error clippedField 8 0 t 0 ht.1 le_rfl
    f g (fun r => clippedField (g r)) clippedField_lipschitz
    (fun r hr => (hf r ⟨hr.1,hr.2.trans ht.2⟩).continuousAt.continuousWithinAt)
    (fun r hr => hf r ⟨hr.1,hr.2.le.trans ht.2⟩)
    (fun r hr => (hg r ⟨hr.1,hr.2.trans ht.2⟩).continuousAt.continuousWithinAt)
    (fun r hr => hg r ⟨hr.1,hr.2.le.trans ht.2⟩)
    (fun r _ => by simp)
  apply dist_le_zero.mp
  simpa only [h0, dist_self, zero_mul, zero_add] using he

/-- Every actual clipped trajectory starting in the checked ball is an
original-field trajectory throughout the step, and its endpoint lies in the
computed inflated ball. No true-trajectory tube assumption is required. -/
theorem clipped_trajectory_ballCanonicalStep {S : ℕ} (hS : 0<S) {h : ℚ}
    (hh : 0 ≤ h) (hhmax : h ≤ 1/100) {b : BallVector} (hb : BallCanonicalMargin b)
    {w : ℝ → WeightedState} (hw0 : ∀ i, (b i).Contains (w 0 i))
    (hw : ∀ t ∈ Icc 0 (h:ℝ), HasDerivAt w (clippedField (w t)) t) :
    (∀ t ∈ Icc 0 (h:ℝ), HasDerivAt w (weightedField (w t)) t) ∧
      (∀ t ∈ Icc 0 (h:ℝ), w t ∈ weightedTube) ∧
      (∀ i : Fin 7, (ballCanonicalStep S h b)[i.val].Contains (w (h:ℝ) i)) := by
  obtain ⟨z, hz0, hz, htube, hend⟩ :=
    exists_ballCanonicalStep hS hh hhmax hw0 (hb.contains_margin hw0)
  have hzc : ∀ t ∈ Icc 0 (h:ℝ), HasDerivAt z (clippedField (z t)) t := by
    intro t ht
    simpa only [clippedField_eq (htube t ht)] using hz t ht
  have heq := clipped_step_unique hw hzc hz0.symm
  have hwt : ∀ t ∈ Icc 0 (h:ℝ), w t ∈ weightedTube := by
    intro t ht
    simpa only [heq ht] using htube t ht
  refine ⟨fun t ht => ?_, hwt, fun i => ?_⟩
  · simpa only [clippedField_eq (hwt t ht)] using hw t ht
  · have hh' : (0:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
    simpa only [heq ⟨hh',le_rfl⟩] using hend i

theorem checked_clipped_trajectory_ballCanonicalStep {S : ℕ} (hS : 0<S) {h : ℚ}
    (hh : 0 ≤ h) (hhmax : h ≤ 1/100) {b : BallVector}
    (hb : checkBallCanonicalMargin b = true)
    {w : ℝ → WeightedState} (hw0 : ∀ i, (b i).Contains (w 0 i))
    (hw : ∀ t ∈ Icc 0 (h:ℝ), HasDerivAt w (clippedField (w t)) t) :
    (∀ t ∈ Icc 0 (h:ℝ), HasDerivAt w (weightedField (w t)) t) ∧
      (∀ t ∈ Icc 0 (h:ℝ), w t ∈ weightedTube) ∧
      (∀ i : Fin 7, (ballCanonicalStep S h b)[i.val].Contains (w (h:ℝ) i)) :=
  clipped_trajectory_ballCanonicalStep hS hh hhmax (checkBallCanonicalMargin_sound hb) hw0 hw

end CentroidEscape

#print axioms CentroidEscape.exists_ballCanonicalStep

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
  logInfo m!"Ball-step audit passed for {checked} declarations."
