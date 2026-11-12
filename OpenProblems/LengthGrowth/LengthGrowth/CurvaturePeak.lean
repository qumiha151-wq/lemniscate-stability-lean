import LengthGrowth.StressIntegralEstimates
import Mathlib.Algebra.Field.Periodic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! The actual periodic curvature attains a positive global maximum.
Its derivative vanishes there. This supplies the peak required in the
stress contradiction argument, rather than assuming one as input. -/

noncomputable section
open Set
namespace LengthGrowth.ClosedFrenetCurve

variable (c : LengthGrowth.ClosedFrenetCurve)

theorem periodic_representative {α : Type*} {f : ℝ → α}
    (hp : Function.Periodic f c.period) (s : ℝ) :
    ∃ u ∈ Icc 0 c.period, f u = f s := by
  have h : f s ∈ Set.range f := ⟨s, rfl⟩
  rw [← hp.image_Icc c.period_pos 0] at h
  simpa using h

theorem exists_curvature_peak : ∃ s₀ ∈ Icc 0 c.period,
    0 < |c.curvature s₀| ∧ c.curvature₁ s₀ = 0 ∧
      ∀ s, |c.curvature s| ≤ |c.curvature s₀| := by
  obtain ⟨s₀, hs₀, hpeak⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc 0 c.period).Nonempty from ⟨0, le_rfl, c.period_pos.le⟩)
    c.curvature_continuous.abs.continuousOn
  have hglobal (s : ℝ) : |c.curvature s| ≤ |c.curvature s₀| := by
    obtain ⟨u, hu, heq⟩ := c.periodic_representative c.curvature_periodic s
    rw [← heq]
    exact hpeak hu
  have hne : c.curvature s₀ ≠ 0 := by
    intro heq
    have hz : c.curvature = fun _ => 0 := by
      funext s
      have h := hglobal s
      rw [heq, abs_zero] at h
      exact abs_nonpos_iff.mp h
    have he := c.energy_pos
    simp [energy, hz] at he
  have hlocal : IsLocalMax (fun s => c.curvature s^2) s₀ := by
    apply Filter.Eventually.of_forall
    intro s
    have h := (sq_le_sq₀ (abs_nonneg (c.curvature s))
      (abs_nonneg (c.curvature s₀))).mpr (hglobal s)
    simpa only [sq_abs] using h
  have hd : HasDerivAt (fun s => c.curvature s^2)
      (2*c.curvature s₀*c.curvature₁ s₀) s₀ := by
    convert! (c.curvature_deriv s₀).pow 2 using 1
    simp
  have hz := hlocal.hasDerivAt_eq_zero hd
  have hk₁ : c.curvature₁ s₀ = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · exact False.elim ((mul_ne_zero (by norm_num) hne) h)
    · exact h
  exact ⟨s₀, hs₀, abs_pos.mpr hne, hk₁, hglobal⟩

theorem stress_nonzero_of_interval
    (h : ∀ s ∈ Icc 0 c.period, c.stress s ≠ 0) :
    ∀ s, c.stress s ≠ 0 := by
  intro s
  obtain ⟨u, hu, heq⟩ := c.periodic_representative c.stress_periodic s
  rw [← heq]
  exact h u hu

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
  logInfo m!"LengthGrowth curvature-peak audit passed for {checked} declarations."
