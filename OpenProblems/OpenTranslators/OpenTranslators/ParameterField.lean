import OpenTranslators.Geometry

/-! The actual scalar field which removes the translator's tangential velocity,
and an explicitly bounded globally Lipschitz time regularization. -/
namespace OpenTranslator.TranslatorParameter
noncomputable section
open Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

def parameterField (z : ℝ → TranslatorState) (s : ℝ) : ℝ := -Real.cos (z s 0)

def parameterDenominator (z : ℝ → TranslatorState) (s : ℝ) : ℝ :=
  regularizingDenominator (z s)

def regularizedParameterField (z : ℝ → TranslatorState) (s : ℝ) : ℝ :=
  parameterField z s/parameterDenominator z s

def regularizedParameterDerivative (z : ℝ → TranslatorState) (s : ℝ) : ℝ :=
  ((z s 1*Real.sin (z s 0))*parameterDenominator z s-
    parameterField z s*(2*z s 2*Real.sin (z s 0)))/(parameterDenominator z s)^2

variable {z : ℝ → TranslatorState}
variable (hz : ∀ s, HasDerivAt z (translatorNumerator (z s)) s)
include hz

theorem parameterField_smooth : ContDiff ℝ ∞ (parameterField z) :=
  (contDiff_pi.mp (global_translator_smooth hz) 0).cos.neg

theorem parameterDenominator_smooth : ContDiff ℝ ∞ (parameterDenominator z) :=
  regularizingDenominator_smooth.comp (global_translator_smooth hz)

theorem parameterField_hasDerivAt (s : ℝ) :
    HasDerivAt (parameterField z) (z s 1*Real.sin (z s 0)) s := by
  convert (TranslatorGeometry.theta_hasDerivAt hz s).cos.neg using 1 <;>
    first | rfl | ring

theorem parameterDenominator_hasDerivAt (s : ℝ) :
    HasDerivAt (parameterDenominator z) (2*z s 2*Real.sin (z s 0)) s := by
  convert denominator_hasDerivAt (hz s) using 1 <;>
    first | rfl | (dsimp [denominatorVariation,translatorNumerator]; ring)

theorem regularizedParameterField_hasDerivAt (s : ℝ) :
    HasDerivAt (regularizedParameterField z) (regularizedParameterDerivative z s) s :=
  (parameterField_hasDerivAt hz s).fun_div (parameterDenominator_hasDerivAt hz s)
    (regularizingDenominator_ne_zero (z s))

omit hz in
theorem parameterField_abs_le_one (z : ℝ → TranslatorState) (s : ℝ) :
    |parameterField z s| ≤ 1 := by
  simpa only [parameterField,abs_neg] using Real.abs_cos_le_one (z s 0)

omit hz in
theorem regularizedParameterField_norm_le (z : ℝ → TranslatorState) (s : ℝ) :
    ‖regularizedParameterField z s‖ ≤ 1 := by
  have hD : 0<parameterDenominator z s := regularizingDenominator_pos (z s)
  rw [Real.norm_eq_abs,regularizedParameterField,abs_div,
    abs_of_pos hD]
  apply (div_le_iff₀ hD).mpr
  exact (parameterField_abs_le_one z s).trans (by
    simpa only [one_mul,parameterDenominator] using regularizingDenominator_ge_one (z s))

omit hz in
theorem regularizedParameterDerivative_norm_le (z : ℝ → TranslatorState) (s : ℝ) :
    ‖regularizedParameterDerivative z s‖ ≤ 4 := by
  have hD : 0<parameterDenominator z s := regularizingDenominator_pos (z s)
  have hD1 : 1≤parameterDenominator z s := regularizingDenominator_ge_one (z s)
  have hk : |z s 1*Real.sin (z s 0)| ≤ 2*parameterDenominator z s := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)).trans
      (by simpa only [mul_one,parameterDenominator] using abs_curvature_le_two_denominator (z s))
  have hv : |2*z s 2*Real.sin (z s 0)| ≤ 2*parameterDenominator z s := by
    rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    calc
      _ ≤ 2 * |z s 2| * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity)
      _ ≤ _ := by
        have hvb : |z s 2|≤parameterDenominator z s := abs_velocity_le_denominator (z s)
        nlinarith
  rw [Real.norm_eq_abs,regularizedParameterDerivative,abs_div,
    abs_of_pos (sq_pos_of_pos hD)]
  apply (div_le_iff₀ (sq_pos_of_pos hD)).mpr
  calc
    _ ≤ |(z s 1*Real.sin (z s 0))*parameterDenominator z s|+
        |parameterField z s*(2*z s 2*Real.sin (z s 0))| := abs_sub _ _
    _ = |z s 1*Real.sin (z s 0)| * parameterDenominator z s+
        |parameterField z s| * |2*z s 2*Real.sin (z s 0)| := by
      simp only [abs_mul,abs_of_pos hD]
    _ ≤ (2*parameterDenominator z s)*parameterDenominator z s+
        1*(2*parameterDenominator z s) :=
      add_le_add (mul_le_mul_of_nonneg_right hk hD.le)
        (mul_le_mul (parameterField_abs_le_one z s) hv (abs_nonneg _) zero_le_one)
    _ ≤ 4*parameterDenominator z s^2 := by
      change 1≤parameterDenominator z s at hD1
      nlinarith [sq_nonneg (parameterDenominator z s-1)]

theorem regularizedParameterField_lipschitz : LipschitzWith 4 (regularizedParameterField z) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun s => (regularizedParameterField_hasDerivAt hz s).differentiableAt)
  intro s
  rw [(regularizedParameterField_hasDerivAt hz s).deriv]
  exact_mod_cast regularizedParameterDerivative_norm_le z s

end
end OpenTranslator.TranslatorParameter

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`OpenTranslator).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Parameter field audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Parameter field audit passed for {count} declarations."
