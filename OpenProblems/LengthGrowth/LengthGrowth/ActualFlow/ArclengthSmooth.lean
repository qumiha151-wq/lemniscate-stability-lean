import LengthGrowth.ActualFlow.ArclengthCoordinate
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-! Actual differentiability and smoothness of the globally constructed inverse.
Finite-order bootstrapping uses only its proved reciprocal-speed derivative.
The resulting position is periodic and genuinely unit speed. -/

noncomputable section
open Filter
open scoped ContDiff Topology

namespace LengthGrowth.ActualFlow.PeriodicRegularPosition

variable (c : PeriodicRegularPosition)

theorem inverse_hasDerivAt (s : ℝ) :
    HasDerivAt c.arclengthInverse (speed c.position (c.arclengthInverse s))⁻¹ s :=
  HasDerivAt.of_local_left_inverse c.inverse_continuous.continuousAt
    (c.arclength_hasDerivAt (c.arclengthInverse s))
    (ne_of_gt (speed_pos c.regular (c.arclengthInverse s)))
    (Eventually.of_forall c.arclength_inverse_left)

theorem inverse_deriv : deriv c.arclengthInverse =
    fun s => (speed c.position (c.arclengthInverse s))⁻¹ :=
  funext fun s => (c.inverse_hasDerivAt s).deriv

theorem inverse_deriv_pos (s : ℝ) : 0 < deriv c.arclengthInverse s := by
  rw [c.inverse_deriv]
  exact inv_pos.mpr (speed_pos c.regular (c.arclengthInverse s))

theorem inverse_contDiff_nat (n : ℕ) : ContDiff ℝ n c.arclengthInverse := by
  induction n with
  | zero => exact contDiff_zero.mpr c.inverse_continuous
  | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
        contDiff_succ_iff_deriv]
      refine ⟨fun s => (c.inverse_hasDerivAt s).differentiableAt, ?_, ?_⟩
      · simp
      · rw [c.inverse_deriv]
        exact (((speed_smooth c.smooth c.regular).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).comp ih).inv
          (fun s => ne_of_gt (speed_pos c.regular (c.arclengthInverse s)))

theorem inverse_smooth : ContDiff ℝ ∞ c.arclengthInverse := by
  rw [contDiff_iff_forall_nat_le]
  intro n _
  exact c.inverse_contDiff_nat n

theorem unitSpeedPosition_smooth : ContDiff ℝ ∞ c.unitSpeedPosition :=
  c.smooth.comp c.inverse_smooth

theorem unitSpeedPosition_periodic : Function.Periodic c.unitSpeedPosition c.length := by
  intro s
  change c.position (c.arclengthInverse (s + c.length)) =
    c.position (c.arclengthInverse s)
  rw [c.inverse_add_length]
  exact c.periodic (c.arclengthInverse s)

theorem unitSpeedPosition_hasDerivAt (s : ℝ) :
    HasDerivAt c.unitSpeedPosition (tangent c.position (c.arclengthInverse s)) s :=
  (c.smooth.differentiable (by simp) (c.arclengthInverse s)).hasDerivAt.scomp s
    (c.inverse_hasDerivAt s)

theorem unitSpeedPosition_unit_speed (s : ℝ) : ‖deriv c.unitSpeedPosition s‖ = 1 := by
  rw [(c.unitSpeedPosition_hasDerivAt s).deriv]
  exact tangent_unit c.regular (c.arclengthInverse s)

theorem unitSpeedPosition_regular (s : ℝ) : deriv c.unitSpeedPosition s ≠ 0 := by
  intro h
  have hu := c.unitSpeedPosition_unit_speed s
  rw [h, norm_zero] at hu
  norm_num at hu

end LengthGrowth.ActualFlow.PeriodicRegularPosition

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`LengthGrowth.ActualFlow).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext, `Classical.choice, `Quot.sound] : Array Name).contains axiomName do
          throwError "Arclength smooth audit failed: {name} depends on {axiomName}"
      count := count + 1
  logInfo m!"ACTUAL_ARCLENGTH_SMOOTH_AUDIT {count}: standard three axioms only."
