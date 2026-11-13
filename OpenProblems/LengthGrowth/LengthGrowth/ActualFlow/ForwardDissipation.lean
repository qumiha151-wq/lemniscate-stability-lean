import LengthGrowth.ActualFlow.ForwardGeometry
import LengthGrowth.ActualFlow.CurveFirstVariation
import LengthGrowth.SubsqrtGrowth

/-! Actual normal FEF on positive time, with endpoint integral laws and restart
estimates through time zero. The only dynamical premise is the actual position
PDE. No backward FEF, assumed dissipation law, or zero limiting energy is used. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth.ActualFlow.ForwardImmersion

variable (c : ForwardImmersion)

/-- Forward normal velocity, required only at strictly positive times. -/
def IsNormalFEF : Prop :=
  ∀ t, 0 < t → ∀ u, HasDerivAt (fun x => c.position x u)
    (-(force (c.position t) u : ℂ) * normal (c.position t) u) t

theorem interior_isNormalFEF (hflow : c.IsNormalFEF) : c.interior.IsNormalFEF := hflow

theorem length_hasDerivAt_normal (hflow : c.IsNormalFEF) {t : ℝ} (ht : 0 < t) :
    HasDerivAt c.length (c.lengthRate t) t :=
  c.interior.length_hasDerivAt_normal (c.interior_isNormalFEF hflow) ht

theorem energy_hasDerivAt_normal (hflow : c.IsNormalFEF) {t : ℝ} (ht : 0 < t) :
    HasDerivAt c.energy (-c.dissipation t) t :=
  c.interior.energy_hasDerivAt_normal (c.interior_isNormalFEF hflow) ht

theorem energy_sq_hasDerivAt_normal (hflow : c.IsNormalFEF) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => c.energy x ^ 2) (-(2 * c.energy t * c.dissipation t)) t :=
  c.interior.energy_sq_hasDerivAt_normal (c.interior_isNormalFEF hflow) ht

/-- The genuine integral energy law, including a one-sided initial endpoint. -/
theorem energy_add_integral_dissipation (hflow : c.IsNormalFEF) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    c.energy t + (∫ x in s..t, c.dissipation x) = c.energy s := by
  have hsub : Icc s t ⊆ Ici 0 := fun x hx => hs.trans hx.1
  have hc := c.dissipation_continuousOn.mono hsub
  have hi : IntervalIntegrable (fun x => -c.dissipation x) volume s t :=
    (hc.neg).intervalIntegrable_of_Icc hst
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst
    (c.energy_continuousOn.mono hsub)
    (fun x hx => c.energy_hasDerivAt_normal hflow (lt_of_le_of_lt hs hx.1)) hi
  rw [intervalIntegral.integral_neg] at he
  linarith

theorem length_sub_eq_integral_lengthRate (hflow : c.IsNormalFEF) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    c.length t - c.length s = ∫ x in s..t, c.lengthRate x := by
  have hsub : Icc s t ⊆ Ici 0 := fun x hx => hs.trans hx.1
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst
    (c.length_continuousOn.mono hsub)
    (fun x hx => c.length_hasDerivAt_normal hflow (lt_of_le_of_lt hs hx.1))
    ((c.lengthRate_continuousOn.mono hsub).intervalIntegrable_of_Icc hst)).symm

/-- Restart inequality for actual length and bending energy. Both endpoints
may be initial time; differentiation is used only in the open time interval. -/
theorem secant_sq_le_energy_drop (hflow : c.IsNormalFEF) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    (c.length t - c.length s) ^ 2 ≤
      (t - s) * (c.energy s ^ 2 - c.energy t ^ 2) := by
  rcases eq_or_lt_of_le hst with h | h
  · subst t
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, le_refl]
  · have hsub : Icc s t ⊆ Ici 0 := fun x hx => hs.trans hx.1
    apply FreeElasticScalar.secant_sq_le_energy_drop c.length (fun x => c.energy x ^ 2)
      c.lengthRate (fun x => -(2 * c.energy x * c.dissipation x)) s t h
      (c.length_continuousOn.mono hsub) ((c.energy_continuousOn.pow 2).mono hsub)
    · intro x hx
      exact c.length_hasDerivAt_normal hflow (lt_of_le_of_lt hs hx.1)
    · intro x hx
      exact c.energy_sq_hasDerivAt_normal hflow (lt_of_le_of_lt hs hx.1)
    · intro x hx
      simpa only [neg_neg] using c.lengthRate_sq_le (hsub ⟨hx.1.le, hx.2.le⟩)

/-- For a global forward classical normal FEF with the stated actual initial
jet regularity, length is little-o of sqrt(time). This is not a fourth-root
growth estimate or an existence theorem for arbitrary initial curves. -/
theorem length_div_sqrt_tendsto_zero (hflow : c.IsNormalFEF) :
    Tendsto (fun t => c.length t / Real.sqrt t) atTop (𝓝 0) := by
  apply FreeElasticScalar.restart_length_div_sqrt_tendsto_zero
    (L := c.length) (H := fun t => c.energy t ^ 2)
  · intro s _
    exact sq_nonneg _
  · intro s t hs hst
    exact c.secant_sq_le_energy_drop hflow hs hst

end LengthGrowth.ActualFlow.ForwardImmersion

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (n, _) in (← getEnv).constants do
    if (`LengthGrowth.ActualFlow).isPrefixOf n || (`FreeElasticScalar).isPrefixOf n then
      for a in (← collectAxioms n) do
        unless allowed.contains a do throwError "Unexpected axiom {a} in {n}"
      count := count + 1
  logInfo m!"Actual forward dissipation and subsqrt growth: {count} declarations, standard axioms only."
