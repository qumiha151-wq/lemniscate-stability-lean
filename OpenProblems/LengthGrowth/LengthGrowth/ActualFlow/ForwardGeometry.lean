import LengthGrowth.ActualFlow.FamilyIntegrals
import LengthGrowth.ActualFlow.FourJetForce
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Forward position data, with actual spatial jets continuous at the initial
time. There is no backward flow, independently supplied force, or integral law
in this record. The normal PDE is imposed separately in ForwardDissipation. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth.ActualFlow

structure ForwardImmersion where
  period : ℝ
  period_pos : 0 < period
  position : ℝ → ℝ → ℂ
  periodic : ∀ t, 0 ≤ t → Function.Periodic (position t) period
  initial_smooth : ContDiff ℝ ∞ (position 0)
  interior_joint_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => position z.1 z.2) (Ioi 0 ×ˢ (univ : Set ℝ))
  immersion : ∀ t, 0 ≤ t → ∀ u, deriv (position t) u ≠ 0
  spatial_jets_continuous : ∀ j : ℕ, j ≤ 4 → ContinuousOn
    (fun z : ℝ × ℝ => iteratedDeriv j (position z.1) z.2)
    (Ici 0 ×ˢ (univ : Set ℝ))

/-- Compactness on every finite forward slab supplies parameter-integral
continuity, including the one-sided initial endpoint. -/
theorem continuousOn_intervalIntegral_forward {F : ℝ → ℝ → ℝ} {a b : ℝ}
    (hF : ContinuousOn (fun z : ℝ × ℝ => F z.1 z.2) (Ici 0 ×ˢ uIcc a b)) :
    ContinuousOn (fun t => ∫ u in a..b, F t u) (Ici 0) := by
  intro t ht
  have hc := continuousOn_intervalIntegral_on_closed_slab
    (F := F) (c := 0) (d := t + 1)
    (hF.mono (by intro z hz; exact ⟨hz.1.1, hz.2⟩))
  apply (hc t ⟨ht, by linarith⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iic_mem_nhds (show t < t + 1 by linarith))] with x hx hy
  exact ⟨hx, hy⟩

namespace ForwardImmersion

variable (c : ForwardImmersion)

def interior : SmoothPeriodicImmersion (Ioi 0) where
  time_open := isOpen_Ioi
  period := c.period
  period_pos := c.period_pos
  position := c.position
  joint_smooth := c.interior_joint_smooth
  periodic := fun t ht => c.periodic t ht.le
  immersion := fun t ht => c.immersion t ht.le

theorem position_slice_smooth {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (c.position t) := by
  rcases eq_or_lt_of_le ht with h | h
  · simpa only [← h] using c.initial_smooth
  · exact c.interior.position_slice_smooth h

theorem jet1_continuousOn : ContinuousOn
    (fun z : ℝ × ℝ => positionJet1 (c.position z.1) z.2) (Ici 0 ×ˢ univ) := by
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero, positionJet1] using
    c.spatial_jets_continuous 1 (by norm_num)

theorem jet2_continuousOn : ContinuousOn
    (fun z : ℝ × ℝ => positionJet2 (c.position z.1) z.2) (Ici 0 ×ˢ univ) := by
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero, positionJet1, positionJet2] using
    c.spatial_jets_continuous 2 (by norm_num)

theorem jet3_continuousOn : ContinuousOn
    (fun z : ℝ × ℝ => positionJet3 (c.position z.1) z.2) (Ici 0 ×ˢ univ) := by
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero, positionJet1, positionJet2,
    positionJet3] using c.spatial_jets_continuous 3 (by norm_num)

theorem jet4_continuousOn : ContinuousOn
    (fun z : ℝ × ℝ => positionJet4 (c.position z.1) z.2) (Ici 0 ×ˢ univ) := by
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero, positionJet1, positionJet2,
    positionJet3, positionJet4] using c.spatial_jets_continuous 4 (by norm_num)

theorem speed_continuousOn : ContinuousOn
    (fun z : ℝ × ℝ => speed (c.position z.1) z.2) (Ici 0 ×ˢ univ) :=
  c.jet1_continuousOn.norm

theorem curvature_continuousOn : ContinuousOn
    (fun z : ℝ × ℝ => curvature (c.position z.1) z.2) (Ici 0 ×ˢ univ) := by
  have hc : ContinuousOn (fun z : ℝ × ℝ =>
      determinant (positionJet1 (c.position z.1) z.2)
        (positionJet2 (c.position z.1) z.2) / speed (c.position z.1) z.2 ^ 3)
      (Ici 0 ×ˢ univ) := by
    intro z hz
    exact (determinant_tendsto (c.jet1_continuousOn z hz) (c.jet2_continuousOn z hz)).div
      ((c.speed_continuousOn z hz).pow 3)
      (pow_ne_zero 3 (speed_pos (c.immersion z.1 hz.1) z.2).ne')
  apply hc.congr
  intro z hz
  exact curvature_eq_two_jet (c.position_slice_smooth hz.1) (c.immersion z.1 hz.1) z.2

theorem force_continuousOn : ContinuousOn
    (fun z : ℝ × ℝ => force (c.position z.1) z.2) (Ici 0 ×ˢ univ) := by
  have hc : ContinuousOn (fun z : ℝ × ℝ => fourJetForceValue
      (positionJet1 (c.position z.1) z.2) (positionJet2 (c.position z.1) z.2)
      (positionJet3 (c.position z.1) z.2) (positionJet4 (c.position z.1) z.2))
      (Ici 0 ×ˢ univ) := by
    intro z hz
    exact fourJetForceValue_tendsto (c.jet1_continuousOn z hz) (c.jet2_continuousOn z hz)
      (c.jet3_continuousOn z hz) (c.jet4_continuousOn z hz) (c.immersion z.1 hz.1 z.2)
  apply hc.congr
  intro z hz
  exact force_eq_fourJetForceValue (c.position_slice_smooth hz.1) (c.immersion z.1 hz.1) z.2

def length : ℝ → ℝ := c.interior.length
def energy : ℝ → ℝ := c.interior.energy
def dissipation : ℝ → ℝ := c.interior.dissipation
def lengthRate : ℝ → ℝ := c.interior.lengthRate

theorem length_nonneg (t : ℝ) : 0 ≤ c.length t := c.interior.length_nonneg t
theorem energy_nonneg (t : ℝ) : 0 ≤ c.energy t := c.interior.energy_nonneg t
theorem dissipation_nonneg (t : ℝ) : 0 ≤ c.dissipation t := c.interior.dissipation_nonneg t

theorem lengthRate_sq_le {t : ℝ} (ht : 0 ≤ t) :
    c.lengthRate t ^ 2 ≤ 2 * c.energy t * c.dissipation t :=
  materialLengthRate_sq_le (c.position_slice_smooth ht) (c.immersion t ht) c.period_pos.le

theorem length_continuousOn : ContinuousOn c.length (Ici 0) :=
  continuousOn_intervalIntegral_forward
    (c.speed_continuousOn.mono (by intro z hz; exact ⟨hz.1, mem_univ _⟩))

theorem energy_continuousOn : ContinuousOn c.energy (Ici 0) := by
  exact (continuousOn_intervalIntegral_forward
    (((c.curvature_continuousOn.pow 2).mul c.speed_continuousOn).mono
      (by intro z hz; exact ⟨hz.1, mem_univ _⟩))).const_mul (1 / 2)

theorem dissipation_continuousOn : ContinuousOn c.dissipation (Ici 0) :=
  continuousOn_intervalIntegral_forward
    (((c.force_continuousOn.pow 2).mul c.speed_continuousOn).mono
      (by intro z hz; exact ⟨hz.1, mem_univ _⟩))

theorem lengthRate_continuousOn : ContinuousOn c.lengthRate (Ici 0) :=
  continuousOn_intervalIntegral_forward
    (((c.curvature_continuousOn.mul c.force_continuousOn).mul c.speed_continuousOn).mono
      (by intro z hz; exact ⟨hz.1, mem_univ _⟩))

end ForwardImmersion
end LengthGrowth.ActualFlow

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (n, _) in (← getEnv).constants do
    if (`LengthGrowth.ActualFlow).isPrefixOf n then
      for a in (← collectAxioms n) do
        unless allowed.contains a do throwError "Unexpected axiom {a} in {n}"
      count := count + 1
  logInfo m!"Actual forward geometry: {count} declarations, standard axioms only."
