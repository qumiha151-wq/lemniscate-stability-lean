import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Util.CollectAxioms

/-! The actual regularized translator vector field. All bounds and regularity
are derived from its formula. This module does not assert that the inverse
time change is global; that requires a separate clock argument. -/

namespace OpenTranslator
noncomputable section
open Set
open scoped ContDiff

abbrev TranslatorState := Fin 3 → ℝ

def regularizingDenominator (z : TranslatorState) : ℝ := 1 + z 2 ^ 2 + z 1 ^ 4 / 4

def translatorNumerator (z : TranslatorState) : TranslatorState :=
  ![z 1, z 2, -(z 1)^3/2 + Real.sin (z 0)]

def regularizedField (z : TranslatorState) : TranslatorState :=
  fun i => translatorNumerator z i / regularizingDenominator z

lemma regularizingDenominator_ge_one (z : TranslatorState) :
    1 ≤ regularizingDenominator z := by
  dsimp [regularizingDenominator]
  nlinarith [sq_nonneg (z 2), sq_nonneg (z 1 ^ 2)]

lemma regularizingDenominator_pos (z : TranslatorState) :
    0 < regularizingDenominator z := lt_of_lt_of_le zero_lt_one (regularizingDenominator_ge_one z)

lemma regularizingDenominator_ne_zero (z : TranslatorState) :
    regularizingDenominator z ≠ 0 := ne_of_gt (regularizingDenominator_pos z)

lemma curvature_sq_le_denominator (z : TranslatorState) :
    z 1 ^ 2 ≤ regularizingDenominator z := by
  dsimp [regularizingDenominator]
  nlinarith [sq_nonneg (z 1 ^ 2 - 2), sq_nonneg (z 2)]

lemma abs_curvature_le_two_denominator (z : TranslatorState) :
    |z 1| ≤ 2 * regularizingDenominator z := by
  have h1 := regularizingDenominator_ge_one z
  have hk := curvature_sq_le_denominator z
  nlinarith [sq_abs (z 1), sq_nonneg (|z 1| - 1)]

lemma abs_velocity_le_denominator (z : TranslatorState) :
    |z 2| ≤ regularizingDenominator z := by
  have h1 := regularizingDenominator_ge_one z
  have hv : z 2 ^ 2 ≤ regularizingDenominator z := by
    dsimp [regularizingDenominator]
    nlinarith [sq_nonneg (z 1 ^ 2)]
  nlinarith [sq_abs (z 2), sq_nonneg (|z 2| - 1)]

lemma abs_curvature_cube_le_four_denominator (z : TranslatorState) :
    |z 1 ^ 3| ≤ 4 * regularizingDenominator z := by
  have hpow : |z 1| ^ 3 ≤ 1 + |z 1| ^ 4 := by
    by_cases h : |z 1| ≤ 1
    · have hh := pow_le_one₀ (n := 3) (abs_nonneg (z 1)) h
      nlinarith [pow_nonneg (abs_nonneg (z 1)) 4]
    · have hh := pow_le_pow_right₀ (le_of_lt (lt_of_not_ge h)) (by decide : 3 ≤ 4)
      linarith
  rw [abs_pow]
  have hp : |z 1| ^ 4 = z 1 ^ 4 := by
    calc
      _ = (|z 1| ^ 2) ^ 2 := by ring
      _ = (z 1 ^ 2) ^ 2 := by rw [sq_abs]
      _ = _ := by ring
  rw [hp] at hpow
  dsimp [regularizingDenominator]
  nlinarith [sq_nonneg (z 2)]

theorem translatorNumerator_abs_le (z : TranslatorState) (i : Fin 3) :
    |translatorNumerator z i| ≤ 3 * regularizingDenominator z := by
  have hD := regularizingDenominator_pos z
  fin_cases i
  · exact (abs_curvature_le_two_denominator z).trans (by linarith)
  · exact (abs_velocity_le_denominator z).trans (by linarith)
  · change |-(z 1)^3/2 + Real.sin (z 0)| ≤ _
    calc
      _ ≤ |-(z 1)^3/2| + |Real.sin (z 0)| := abs_add_le _ _
      _ = |z 1 ^ 3| / 2 + |Real.sin (z 0)| := by simp [abs_div]
      _ ≤ 3 * regularizingDenominator z := by
        linarith [abs_curvature_cube_le_four_denominator z,
          Real.abs_sin_le_one (z 0), regularizingDenominator_ge_one z]

/-- A uniform bound for the actual rescaled vector field. -/
theorem regularizedField_norm_le (z : TranslatorState) : ‖regularizedField z‖ ≤ 3 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 3)).mpr
  intro i
  rw [Real.norm_eq_abs, regularizedField, abs_div,
    abs_of_pos (regularizingDenominator_pos z)]
  exact (div_le_iff₀ (regularizingDenominator_pos z)).mpr (translatorNumerator_abs_le z i)

theorem regularizingDenominator_smooth : ContDiff ℝ ∞ regularizingDenominator := by
  unfold regularizingDenominator
  fun_prop

theorem translatorNumerator_smooth : ContDiff ℝ ∞ translatorNumerator := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [translatorNumerator] <;> fun_prop

/-- Smoothness is global because the actual denominator is at least one. -/
theorem regularizedField_smooth : ContDiff ℝ ∞ regularizedField := by
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_pi.mp translatorNumerator_smooth i).div regularizingDenominator_smooth
    regularizingDenominator_ne_zero

def denominatorVariation (z h : TranslatorState) : ℝ :=
  2 * z 2 * h 2 + z 1 ^ 3 * h 1

def numeratorVariation (z h : TranslatorState) : TranslatorState :=
  ![h 1, h 2, -(3/2:ℝ) * z 1 ^ 2 * h 1 + Real.cos (z 0) * h 0]

def regularizedVariation (z h : TranslatorState) : TranslatorState := fun i =>
  (numeratorVariation z h i * regularizingDenominator z -
    translatorNumerator z i * denominatorVariation z h) / regularizingDenominator z ^ 2

theorem denominator_hasDerivAt {x : ℝ → TranslatorState} {h : TranslatorState} {t : ℝ}
    (hx : HasDerivAt x h t) :
    HasDerivAt (fun u => regularizingDenominator (x u)) (denominatorVariation (x t) h) t := by
  have h1 := hasDerivAt_pi.mp hx 1
  have h2 := hasDerivAt_pi.mp hx 2
  convert ((h2.pow 2).const_add 1).add ((h1.pow 4).div_const 4) using 1 <;>
    first | rfl | (simp only [denominatorVariation]; ring)

theorem numerator_hasDerivAt {x : ℝ → TranslatorState} {h : TranslatorState} {t : ℝ}
    (hx : HasDerivAt x h t) :
    HasDerivAt (fun u => translatorNumerator (x u)) (numeratorVariation (x t) h) t := by
  have h0 := hasDerivAt_pi.mp hx 0
  have h1 := hasDerivAt_pi.mp hx 1
  have h2 := hasDerivAt_pi.mp hx 2
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact h1
  · exact h2
  · change HasDerivAt (fun u => -(x u 1)^3/2 + Real.sin (x u 0))
      (-(3/2:ℝ) * x t 1 ^ 2 * h 1 + Real.cos (x t 0) * h 0) t
    convert ((h1.pow 3).neg.div_const 2).add h0.sin using 1 <;>
      first | rfl | ring

/-- Actual derivatives along every differentiable state path. -/
theorem regularizedField_hasDerivAt {x : ℝ → TranslatorState} {h : TranslatorState} {t : ℝ}
    (hx : HasDerivAt x h t) :
    HasDerivAt (fun u => regularizedField (x u)) (regularizedVariation (x t) h) t := by
  apply hasDerivAt_pi.mpr
  intro i
  exact (hasDerivAt_pi.mp (numerator_hasDerivAt hx) i).div
    (denominator_hasDerivAt hx) (regularizingDenominator_ne_zero (x t))

lemma denominatorVariation_abs_le (z h : TranslatorState) :
    |denominatorVariation z h| ≤ 6 * regularizingDenominator z * ‖h‖ := by
  have hD := regularizingDenominator_pos z
  have hh (i : Fin 3) : |h i| ≤ ‖h‖ := norm_le_pi_norm h i
  have hv := abs_velocity_le_denominator z
  have hk := abs_curvature_cube_le_four_denominator z
  calc
    _ ≤ |2 * z 2 * h 2| + |z 1 ^ 3 * h 1| := abs_add_le _ _
    _ = (2 * |z 2|) * |h 2| + |z 1 ^ 3| * |h 1| := by simp [abs_mul]
    _ ≤ (2 * regularizingDenominator z) * ‖h‖ +
        (4 * regularizingDenominator z) * ‖h‖ :=
      add_le_add (mul_le_mul (by linarith) (hh 2) (abs_nonneg _) (by positivity))
        (mul_le_mul hk (hh 1) (abs_nonneg _) (by positivity))
    _ = _ := by ring

lemma numeratorVariation_abs_le (z h : TranslatorState) (i : Fin 3) :
    |numeratorVariation z h i| ≤ 3 * regularizingDenominator z * ‖h‖ := by
  have hD := regularizingDenominator_ge_one z
  have hDpos := regularizingDenominator_pos z
  have hn := norm_nonneg h
  have hh (i : Fin 3) : |h i| ≤ ‖h‖ := norm_le_pi_norm h i
  have hsmall : ‖h‖ ≤ 3 * regularizingDenominator z * ‖h‖ := by nlinarith
  fin_cases i
  · exact (hh 1).trans hsmall
  · exact (hh 2).trans hsmall
  · change |-(3/2:ℝ) * z 1 ^ 2 * h 1 + Real.cos (z 0) * h 0| ≤ _
    have hk := curvature_sq_le_denominator z
    calc
      _ ≤ |-(3/2:ℝ) * z 1 ^ 2 * h 1| + |Real.cos (z 0) * h 0| := abs_add_le _ _
      _ = ((3/2:ℝ) * z 1 ^ 2) * |h 1| + |Real.cos (z 0)| * |h 0| := by
        simp [abs_mul, abs_div, abs_pow, sq_abs]
      _ ≤ ((3/2:ℝ) * regularizingDenominator z) * ‖h‖ + 1 * ‖h‖ :=
        add_le_add (mul_le_mul (by linarith) (hh 1) (abs_nonneg _) (by positivity))
          (mul_le_mul (Real.abs_cos_le_one _) (hh 0) (abs_nonneg _) (by positivity))
      _ ≤ _ := by nlinarith

/-- A uniform derivative estimate, obtained from the quotient rule and explicit
polynomial bounds. The deliberately coarse constant is sufficient for existence. -/
theorem regularizedVariation_norm_le (z h : TranslatorState) :
    ‖regularizedVariation z h‖ ≤ 100 * ‖h‖ := by
  have hD := regularizingDenominator_pos z
  have hn := norm_nonneg h
  apply (pi_norm_le_iff_of_nonneg (by positivity : (0:ℝ) ≤ 100 * ‖h‖)).mpr
  intro i
  rw [Real.norm_eq_abs, regularizedVariation, abs_div, abs_of_pos (sq_pos_of_pos hD)]
  apply (div_le_iff₀ (sq_pos_of_pos hD)).mpr
  calc
    _ ≤ |numeratorVariation z h i * regularizingDenominator z| +
        |translatorNumerator z i * denominatorVariation z h| := abs_sub _ _
    _ = |numeratorVariation z h i| * regularizingDenominator z +
        |translatorNumerator z i| * |denominatorVariation z h| := by
      rw [abs_mul, abs_mul, abs_of_pos hD]
    _ ≤ (3 * regularizingDenominator z * ‖h‖) * regularizingDenominator z +
        (3 * regularizingDenominator z) * (6 * regularizingDenominator z * ‖h‖) :=
      add_le_add (mul_le_mul_of_nonneg_right (numeratorVariation_abs_le z h i) hD.le)
        (mul_le_mul (translatorNumerator_abs_le z i) (denominatorVariation_abs_le z h)
          (abs_nonneg _) (by positivity))
    _ ≤ (100 * ‖h‖) * regularizingDenominator z ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg (regularizingDenominator z)) hn]

/-- The actual regularized translator field is globally 100-Lipschitz. -/
theorem regularizedField_lipschitz : LipschitzWith 100 regularizedField := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hline (t : ℝ) : HasDerivAt (fun u : ℝ => y + u • (x - y)) (x - y) t := by
    simpa using ((hasDerivAt_id t).smul_const (x - y)).const_add y
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun u : ℝ => regularizedField (y + u • (x - y)))
    (f' := fun u : ℝ => regularizedVariation (y + u • (x - y)) (x - y))
    (C := 100 * ‖x - y‖)
    (fun t _ => (regularizedField_hasDerivAt (hline t)).hasDerivWithinAt)
    (fun t _ => regularizedVariation_norm_le _ _)
  simpa [dist_eq_norm] using h

end
end OpenTranslator

#print axioms OpenTranslator.regularizedField_lipschitz

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`OpenTranslator).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
      checked := checked + 1
  logInfo m!"RegularizedField: audited {checked} declarations; standard axioms only."
