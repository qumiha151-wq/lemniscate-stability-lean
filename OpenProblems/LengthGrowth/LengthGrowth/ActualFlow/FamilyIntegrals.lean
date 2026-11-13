import LengthGrowth.ActualFlow.FamilyRegularity
import LengthGrowth.ActualFlow.MaterialIntegrals
import LengthGrowth.ActualFlow.CompactParameterIntegral

/-! Geometric integrals of a position-only smooth family on an open time set.
This module proves actual integral derivatives before using the normal-flow
PDE. No time variation of metric or curvature is an input. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace LengthGrowth.ActualFlow.SmoothPeriodicImmersion

variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

def length (t : ℝ) : ℝ := materialLength (c.position t) c.period
def energy (t : ℝ) : ℝ := materialEnergy (c.position t) c.period
def dissipation (t : ℝ) : ℝ := materialDissipation (c.position t) c.period
def lengthRate (t : ℝ) : ℝ := materialLengthRate (c.position t) c.period

theorem length_nonneg (t : ℝ) : 0 ≤ c.length t :=
  materialLength_nonneg _ c.period_pos.le

theorem energy_nonneg (t : ℝ) : 0 ≤ c.energy t :=
  materialEnergy_nonneg _ c.period_pos.le

theorem dissipation_nonneg (t : ℝ) : 0 ≤ c.dissipation t :=
  materialDissipation_nonneg _ c.period_pos.le

theorem lengthRate_sq_le {t : ℝ} (ht : t ∈ I) :
    c.lengthRate t ^ 2 ≤ 2 * c.energy t * c.dissipation t :=
  materialLengthRate_sq_le (c.position_slice_smooth ht) (c.immersion t ht) c.period_pos.le

theorem length_continuousOn : ContinuousOn c.length I :=
  continuousOn_intervalIntegral_of_isOpen c.time_open
    (c.speed_joint_smooth.continuousOn.mono (fun _ hz => ⟨hz.1, mem_univ _⟩))

theorem energy_continuousOn : ContinuousOn c.energy I := by
  have hi := continuousOn_intervalIntegral_of_isOpen (a := 0) (b := c.period) c.time_open
    (F := fun t u => curvature (c.position t) u ^ 2 * speed (c.position t) u)
    (((c.curvature_joint_smooth.pow 2).mul c.speed_joint_smooth).continuousOn.mono
      (fun _ hz => ⟨hz.1, mem_univ _⟩))
  exact continuousOn_const.mul hi

theorem dissipation_continuousOn : ContinuousOn c.dissipation I :=
  continuousOn_intervalIntegral_of_isOpen c.time_open
    (((c.force_joint_smooth.pow 2).mul c.speed_joint_smooth).continuousOn.mono
      (fun _ hz => ⟨hz.1, mem_univ _⟩))

theorem lengthRate_continuousOn : ContinuousOn c.lengthRate I :=
  continuousOn_intervalIntegral_of_isOpen c.time_open
    ((c.curvature_joint_smooth.mul c.force_joint_smooth |>.mul c.speed_joint_smooth).continuousOn.mono
      (fun _ hz => ⟨hz.1, mem_univ _⟩))

theorem length_hasDerivAt_actualTimeDerivative {t : ℝ} (ht : t ∈ I) :
    HasDerivAt c.length
      (∫ u in 0..c.period, deriv (fun x => speed (c.position x) u) t) t :=
  hasDerivAt_intervalIntegral_of_jointC1 c.time_open
    (c.speed_joint_smooth.of_le (by simp)) ht

theorem energy_hasDerivAt_actualTimeDerivative {t : ℝ} (ht : t ∈ I) :
    HasDerivAt c.energy ((1 / 2 : ℝ) *
      ∫ u in 0..c.period, deriv (fun x => curvature (c.position x) u ^ 2 *
        speed (c.position x) u) t) t :=
  (hasDerivAt_intervalIntegral_of_jointC1 (a := 0) (b := c.period) c.time_open
    (((c.curvature_joint_smooth.pow 2).mul c.speed_joint_smooth).of_le (by simp)) ht).const_mul _

end LengthGrowth.ActualFlow.SmoothPeriodicImmersion

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (n, _) in (← getEnv).constants do
    if (`LengthGrowth.ActualFlow).isPrefixOf n then
      for a in (← collectAxioms n) do
        unless allowed.contains a do throwError "Unexpected axiom {a} in {n}"
      count := count + 1
  logInfo m!"Actual family integrals: {count} declarations, standard axioms only."
