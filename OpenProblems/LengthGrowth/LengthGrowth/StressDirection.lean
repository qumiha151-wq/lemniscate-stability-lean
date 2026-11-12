import LengthGrowth.CurvaturePeak

/-! Actual derivative of the unit elastic-stress direction. The factor
`k²` in its speed avoids an uncontrolled square-root of the length. -/

noncomputable section
open Set
namespace LengthGrowth.ClosedFrenetCurve

variable (c : LengthGrowth.ClosedFrenetCurve)

def stressDirection (s : ℝ) : ℂ := c.stress s / (‖c.stress s‖ : ℂ)
def stressDirectionDerivative (s : ℝ) : ℂ :=
  ((c.force s*c.curvature s^2/(2*‖c.stress s‖^3) : ℝ) : ℂ) *
    (Complex.I*c.stress s)

theorem stress_norm_deriv (s : ℝ) (hs : c.stress s ≠ 0) :
    HasDerivAt (fun u => ‖c.stress u‖)
      (c.curvature₁ s*c.force s/‖c.stress s‖) s := by
  have hn : ‖c.stress s‖ ≠ 0 := norm_ne_zero_iff.mpr hs
  have h := (c.stress_norm_sq_deriv s).sqrt (pow_ne_zero 2 hn)
  convert! h using 1
  · funext u
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  · rw [Real.sqrt_sq (norm_nonneg _)]
    field_simp

theorem stress_perpendicular_identity (s : ℝ) :
    ((‖c.stress s‖^2 : ℝ) : ℂ)*c.normal s -
      (c.curvature₁ s : ℂ)*c.stress s =
      ((c.curvature s : ℂ)^2/2)*(Complex.I*c.stress s) := by
  rw [c.stress_norm_sq]
  simp only [Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_div,
    Complex.ofReal_ofNat, stress, normal]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem stressDirection_deriv (s : ℝ) (hs : c.stress s ≠ 0) :
    HasDerivAt c.stressDirection (c.stressDirectionDerivative s) s := by
  have hn : ‖c.stress s‖ ≠ 0 := norm_ne_zero_iff.mpr hs
  have hnC : (‖c.stress s‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  have hw := c.stress_norm_deriv s hs
  convert! (c.stress_deriv s).div hw.ofReal_comp hnC using 1
  have hp := c.stress_perpendicular_identity s
  simp only [Complex.ofReal_pow] at hp
  dsimp [stressDirectionDerivative]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat]
  field_simp [hnC]
  linear_combination -(2*(c.force s : ℂ))*hp

theorem stressDirectionDerivative_norm (s : ℝ) (hs : c.stress s ≠ 0) :
    ‖c.stressDirectionDerivative s‖ =
      c.curvature s^2*|c.force s|/(2*‖c.stress s‖^2) := by
  have hn : 0 < ‖c.stress s‖ := norm_pos_iff.mpr hs
  simp only [stressDirectionDerivative, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_I, one_mul, abs_div, abs_mul, abs_pow,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_pos hn, sq_abs]
  field_simp [hn.ne']

theorem stressDirection_unit (s : ℝ) (hs : c.stress s ≠ 0) :
    ‖c.stressDirection s‖ = 1 := by
  have hn : ‖c.stress s‖ ≠ 0 := norm_ne_zero_iff.mpr hs
  simp [stressDirection, hn]

end LengthGrowth.ClosedFrenetCurve

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`LengthGrowth).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"LengthGrowth stress-direction audit passed for {checked} declarations."
