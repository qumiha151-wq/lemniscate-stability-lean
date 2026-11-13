import LengthGrowth.ActualFlow.ProductWindow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Exact relative energy accounting for a genuine forward normal FEF.
The physical-time window may start at zero. No clock inverse, endpoint
product gain, absolute-curvature cap, or new flow-existence premise is used. -/

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth.ActualFlow.ForwardImmersion

variable (c : ForwardImmersion)

theorem energy_le_of_le (hflow : c.IsNormalFEF) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) : c.energy t ≤ c.energy s := by
  have he := c.energy_add_integral_dissipation hflow hs hst
  have hd : 0 ≤ ∫ x in s..t, c.dissipation x :=
    intervalIntegral.integral_nonneg_of_forall hst c.dissipation_nonneg
  linarith

theorem energy_antitoneOn (hflow : c.IsNormalFEF) :
    AntitoneOn c.energy (Ici 0) := by
  intro s hs t _ht hst
  exact c.energy_le_of_le hflow hs hst

theorem log_energy_continuousOn :
    ContinuousOn (fun x => Real.log (c.energy x)) (Ici 0) :=
  c.energy_continuousOn.log (fun _x hx => ne_of_gt (c.energy_pos hx))

theorem log_energy_hasDerivAt_normal (hflow : c.IsNormalFEF)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => Real.log (c.energy x))
      (-(c.dissipation t / c.energy t)) t := by
  simpa only [neg_div] using
    (c.energy_hasDerivAt_normal hflow ht).log (ne_of_gt (c.energy_pos ht.le))

/-- Relative dissipation is exactly the logarithmic loss of actual energy.
FTC differentiates only at strictly positive interior times. -/
theorem relativeDissipation_eq_log_energy_sub (hflow : c.IsNormalFEF)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    c.relativeDissipation s t = Real.log (c.energy s) - Real.log (c.energy t) := by
  have hsub : Icc s t ⊆ Ici 0 := fun x hx => hs.trans hx.1
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst
    (c.log_energy_continuousOn.mono hsub)
    (fun x hx => c.log_energy_hasDerivAt_normal hflow (lt_of_le_of_lt hs hx.1))
    (((c.relativeDissipation_density_continuousOn.mono hsub).neg).intervalIntegrable_of_Icc hst)
  rw [intervalIntegral.integral_neg] at he
  change -(c.relativeDissipation s t) = _ at he
  linarith

theorem energy_ratio_eq_exp_relativeDissipation (hflow : c.IsNormalFEF)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    c.energy s / c.energy t = Real.exp (c.relativeDissipation s t) := by
  rw [c.relativeDissipation_eq_log_energy_sub hflow hs hst, Real.exp_sub,
    Real.exp_log (c.energy_pos hs), Real.exp_log (c.energy_pos (hs.trans hst))]

theorem energy_eq_terminal_mul_exp_relativeDissipation (hflow : c.IsNormalFEF)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    c.energy s = c.energy t * Real.exp (c.relativeDissipation s t) := by
  have he := c.energy_ratio_eq_exp_relativeDissipation hflow hs hst
  have hn := ne_of_gt (c.energy_pos (hs.trans hst))
  field_simp [hn] at he
  nlinarith

/-- The physical energy budget lies between the two constant endpoint energies. -/
theorem energyFourthBudget_endpoint_bounds (hflow : c.IsNormalFEF)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    c.energy t ^ 4 * (t - s) ≤ c.energyFourthBudget s t ∧
      c.energyFourthBudget s t ≤ c.energy s ^ 4 * (t - s) := by
  have hsub : Icc s t ⊆ Ici 0 := fun x hx => hs.trans hx.1
  have hi : IntervalIntegrable (fun x => c.energy x ^ 4) volume s t :=
    ((c.energy_continuousOn.pow 4).mono hsub).intervalIntegrable_of_Icc hst
  constructor
  · calc
      c.energy t ^ 4 * (t - s) = ∫ _x in s..t, c.energy t ^ 4 := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
      _ ≤ c.energyFourthBudget s t := by
        apply intervalIntegral.integral_mono_on hst intervalIntegrable_const hi
        intro x hx
        exact pow_le_pow_left₀ (c.energy_nonneg t)
          (c.energy_le_of_le hflow (hsub hx) hx.2) 4
  · calc
      c.energyFourthBudget s t ≤ ∫ _x in s..t, c.energy s ^ 4 := by
        apply intervalIntegral.integral_mono_on hst hi intervalIntegrable_const
        intro x hx
        exact pow_le_pow_left₀ (c.energy_nonneg x) (c.energy_le_of_le hflow hs hx.1) 4
      _ = c.energy s ^ 4 * (t - s) := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring

/-- Freezing scale at the actual terminal energy changes the fourth-energy
time budget by at most exp(4Z); the inequalities have the displayed direction. -/
theorem endpoint_energy_fourth_window_bounds (hflow : c.IsNormalFEF)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    c.energyFourthBudget s t * Real.exp (-4 * c.relativeDissipation s t) ≤
        c.energy t ^ 4 * (t - s) ∧
      c.energy t ^ 4 * (t - s) ≤ c.energyFourthBudget s t := by
  have hb := c.energyFourthBudget_endpoint_bounds hflow hs hst
  refine ⟨?_, hb.1⟩
  have he := c.energy_eq_terminal_mul_exp_relativeDissipation hflow hs hst
  have hex : Real.exp (c.relativeDissipation s t) ^ 4 *
      Real.exp (-4 * c.relativeDissipation s t) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    norm_num only [Nat.cast_ofNat, neg_mul, add_neg_cancel, Real.exp_zero]
  calc
    c.energyFourthBudget s t * Real.exp (-4 * c.relativeDissipation s t) ≤
        (c.energy s ^ 4 * (t - s)) * Real.exp (-4 * c.relativeDissipation s t) :=
      mul_le_mul_of_nonneg_right hb.2 (Real.exp_pos _).le
    _ = c.energy t ^ 4 * (t - s) := by
      rw [he, mul_pow]
      calc
        _ = (c.energy t ^ 4 * (t - s)) *
            (Real.exp (c.relativeDissipation s t) ^ 4 *
              Real.exp (-4 * c.relativeDissipation s t)) := by ring
        _ = _ := by rw [hex, mul_one]

theorem relative_energy_loss_eq_exp_sub_one (hflow : c.IsNormalFEF)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (c.energy s - c.energy t) / c.energy t =
      Real.exp (c.relativeDissipation s t) - 1 := by
  rw [sub_div, div_self (ne_of_gt (c.energy_pos (hs.trans hst))),
    c.energy_ratio_eq_exp_relativeDissipation hflow hs hst]

end LengthGrowth.ActualFlow.ForwardImmersion

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`LengthGrowth).isPrefixOf name || (`FreeElasticScalar).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext, `Classical.choice, `Quot.sound] : Array Name).contains axiomName do
          throwError "Actual relative-energy audit failed: {name} depends on {axiomName}"
      count := count + 1
  logInfo m!"ACTUAL_RELATIVE_ENERGY_AUDIT {count}: standard three axioms only."
