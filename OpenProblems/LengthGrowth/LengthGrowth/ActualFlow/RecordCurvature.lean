import LengthGrowth.ActualFlow.RecordSelection

/-! Curvature at a selected time on a high product record window.
Here `relativeDissipation` is the integral of D/E in physical time,
so it is also the weighted integral of D/E⁵ with weight E⁴. -/

noncomputable section
open Set MeasureTheory

namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

theorem exists_dissipation_slice {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∃ x ∈ Icc s t, (c.dissipation x / c.energy x ^ 5) * c.energyFourthBudget s t
      ≤ c.relativeDissipation s t := by
  let d := fun y => c.dissipation y / c.energy y ^ 5
  have hsub : Icc s t ⊆ Ici 0 := fun _ hy => hs.trans hy.1
  have hc : ContinuousOn d (Icc s t) :=
    (c.dissipation_continuousOn.mono hsub).div ((c.energy_continuousOn.mono hsub).pow 5)
      (fun y hy => pow_ne_zero _ (c.energy_pos (hsub hy)).ne')
  obtain ⟨x, hx, hm⟩ := isCompact_Icc.exists_isMinOn ⟨s, le_rfl, hst⟩ hc
  refine ⟨x, hx, ?_⟩
  change d x * (∫ y in s..t, c.energy y ^ 4) ≤ ∫ y in s..t, c.dissipation y / c.energy y
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hst
    ((((c.energy_continuousOn.mono hsub).pow 4).const_mul (d x)).intervalIntegrable_of_Icc hst)
    ((c.relativeDissipation_density_continuousOn.mono hsub).intervalIntegrable_of_Icc hst)
  intro y hy
  calc
    d x * c.energy y ^ 4 ≤ d y * c.energy y ^ 4 :=
      mul_le_mul_of_nonneg_right (hm hy) (pow_nonneg (c.energy_nonneg y) 4)
    _ = _ := by dsimp [d]; field_simp [(c.energy_pos (hsub hy)).ne']

theorem normalized_curvature_six_le {x : ℝ} (hx : 0 ≤ x) (u : ℝ) :
    (|curvature (c.position x) u| / c.energy x) ^ 6 ≤
      16777216 * (c.dissipation x / c.energy x ^ 5) := by
  have h := c.stress_coercivity hx u
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos (c.energy_pos hx) 6)).mpr
  have he : 16777216 * (c.dissipation x / c.energy x ^ 5) * c.energy x ^ 6 =
      16777216 * (c.energy x * c.dissipation x) := by
    field_simp [(c.energy_pos hx).ne']
  rw [he]
  linarith

/-- A single time works for every material point. The record height controls
both normalized dissipation and the sixth power of the normalized curvature. -/
theorem exists_flat_slice_of_unbounded (hflow : c.IsNormalFEF)
    (hnot : ¬ c.HasBoundedEnergyLength) {K : ℝ} (hK : c.normalizedProduct 0 + 2 ≤ K) :
    ∃ t, K ≤ c.normalizedProduct t ∧ ∃ x ∈ Icc 0 t,
      Real.sqrt (c.normalizedProduct t ^ 2 - c.normalizedProduct t) ≤ c.normalizedProduct x ∧
      c.dissipation x / c.energy x ^ 5 ≤ 2 / (c.normalizedProduct t * (c.normalizedProduct t - 1)) ∧
      ∀ u, (|curvature (c.position x) u| / c.energy x) ^ 6 ≤
        33554432 / (c.normalizedProduct t * (c.normalizedProduct t - 1)) := by
  obtain ⟨t, ht, hKt, _, s, hs, hR, _, hZ, _⟩ :=
    c.exists_high_record_window_of_unbounded hflow hnot hK
  have ha := c.high_record_budget_admissible hflow ht (hK.trans hKt)
  obtain ⟨x, hx, hd⟩ := c.exists_dissipation_slice hs.1 hs.2
  rw [hR] at hd
  have hD : c.dissipation x / c.energy x ^ 5 ≤
      2 / (c.normalizedProduct t * (c.normalizedProduct t - 1)) := by
    rw [mul_comm (c.normalizedProduct t), ← div_div]
    exact (le_div_iff₀ ha.1).mpr (hd.trans hZ)
  have hsmall : c.energyFourthBudget s t < c.normalizedProduct t ^ 2 := hR ▸ ha.2.2
  have hprod := c.normalizedProduct_lower_on_window hflow hs.1 hs.2 hsmall hx
  rw [hR] at hprod
  refine ⟨t, hKt, x, ⟨hs.1.trans hx.1, hx.2⟩, hprod, hD, fun u => ?_⟩
  calc
    _ ≤ _ := c.normalized_curvature_six_le (hs.1.trans hx.1) u
    _ ≤ 16777216 * (2 / (c.normalizedProduct t * (c.normalizedProduct t - 1))) :=
      mul_le_mul_of_nonneg_left hD (by norm_num)
    _ = _ := by ring

end LengthGrowth.ActualFlow.ForwardImmersion
