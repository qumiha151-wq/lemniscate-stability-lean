import LengthGrowth.ActualFlow.GrowthEquivalence
import LengthGrowth.ActualFlow.FiniteRecordWindow

/-! Finite record selection on a given actual forward immersion.
Unbounded energy-length product is an explicit conditional premise, not a
conclusion about an arbitrary flow. Records may tie earlier values. No first
arrival time, inverse clock, infinite sequence or ancient limit is defined. -/

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth.ActualFlow.ForwardImmersion

variable (c : ForwardImmersion)

theorem exists_product_above_of_unbounded (hnot : ¬ c.HasBoundedEnergyLength) (K : ℝ) :
    ∃ T, 0 ≤ T ∧ K < c.normalizedProduct T := by
  by_contra h
  push Not at h
  apply hnot
  refine ⟨K, ?_⟩
  intro t ht
  exact h t ht

/-- A maximum on a finite compact interval supplies a record, allowing ties. -/
theorem exists_record_above_of_unbounded (hnot : ¬ c.HasBoundedEnergyLength) (K : ℝ) :
    ∃ t, 0 ≤ t ∧ K ≤ c.normalizedProduct t ∧
      ∀ x ∈ Icc 0 t, c.normalizedProduct x ≤ c.normalizedProduct t := by
  obtain ⟨T, hT, hKT⟩ := c.exists_product_above_of_unbounded hnot K
  have hc := c.normalizedProduct_continuousOn.mono
    (show Icc 0 T ⊆ Ici 0 from fun x hx => hx.1)
  obtain ⟨t, ht, hm⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc 0 T).Nonempty from ⟨0, ⟨le_rfl, hT⟩⟩) hc
  refine ⟨t, ht.1, hKT.le.trans (hm ⟨hT, le_rfl⟩), ?_⟩
  intro x hx
  exact hm ⟨hx.1, hx.2.trans ht.2⟩

/-- Every sufficiently high requested threshold, in the explicitly unbounded
branch, has an actual finite record and the previously proved high window. -/
theorem exists_high_record_window_of_unbounded (hflow : c.IsNormalFEF)
    (hnot : ¬ c.HasBoundedEnergyLength) {K : ℝ}
    (hK : c.normalizedProduct 0 + 2 ≤ K) :
    ∃ t, 0 ≤ t ∧ K ≤ c.normalizedProduct t ∧
      (∀ x ∈ Icc 0 t, c.normalizedProduct x ≤ c.normalizedProduct t) ∧
      ∃ s, s ∈ Icc 0 t ∧ c.energyFourthBudget s t = c.normalizedProduct t ∧
        0 ≤ c.relativeDissipation s t ∧
        c.relativeDissipation s t ≤ 2 / (c.normalizedProduct t - 1) ∧
        c.normalizedProduct t * Real.exp (-8 / (c.normalizedProduct t - 1)) ≤
          c.energy t ^ 4 * (t - s) ∧
        c.energy t ^ 4 * (t - s) ≤ c.normalizedProduct t ∧
        1 ≤ c.energy s / c.energy t ∧
        c.energy s / c.energy t ≤ Real.exp (2 / (c.normalizedProduct t - 1)) ∧
        (∫ x in s..t, c.dissipation x) / c.energy t ≤
          Real.exp (2 / (c.normalizedProduct t - 1)) - 1 := by
  obtain ⟨t, ht, hKt, hrecord⟩ := c.exists_record_above_of_unbounded hnot K
  exact ⟨t, ht, hKt, hrecord, c.exists_high_record_window hflow ht (hK.trans hKt) hrecord⟩

end LengthGrowth.ActualFlow.ForwardImmersion

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (n, _) in (← getEnv).constants do
    if (`LengthGrowth).isPrefixOf n || (`FreeElasticScalar).isPrefixOf n then
      for a in (← collectAxioms n) do
        unless allowed.contains a do throwError "Unexpected axiom {a} in {n}"
      count := count + 1
  logInfo m!"Actual finite record selection: {count} declarations; standard axioms only."
