import LengthGrowth.ActualFlow.ForwardRescaling
import LengthGrowth.ActualFlow.RecordWindowInterior
import LengthGrowth.ActualFlow.RecordCurvature

/-! Finite windows of a flow with unbounded energy-length product, expressed
in the spatial units given by the original terminal energy. -/

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth.ActualFlow.ForwardImmersion

variable (c : ForwardImmersion)

/-- The interval `[0,T]` belongs to the rescaled forward flow `b`.
Its endpoint is the normalized image of the record time `t`. -/
structure RescaledRecordWindow (b : ForwardImmersion) (s t T : ℝ) : Prop where
  start : s ∈ Icc 0 t
  record : ∀ x ∈ Icc 0 t, c.normalizedProduct x ≤ c.normalizedProduct t
  budget : c.energyFourthBudget s t = c.normalizedProduct t
  flow : b.IsNormalFEF
  samePeriod : b.period = c.period
  duration : T = c.energy t ^ 4 * (t - s)
  duration_pos : 0 < T
  duration_bounds : c.normalizedProduct t * Real.exp (-8 / (c.normalizedProduct t - 1)) ≤ T ∧
    T ≤ c.normalizedProduct t
  position : ∀ τ u, b.position τ u = c.energy t • c.position (s + τ / c.energy t ^ 4) u
  centered : ∀ δ ∈ Icc (-T) 0, T + δ ∈ Icc 0 T ∧
    t + δ / c.energy t ^ 4 ∈ Icc s t ∧
    ∀ u, b.position (T + δ) u = c.energy t • c.position (t + δ / c.energy t ^ 4) u
  terminal_energy : b.energy T = 1
  terminal_length : b.length T = c.normalizedProduct t
  action : (∫ τ in 0..T, b.dissipation τ) = Real.exp (c.relativeDissipation s t) - 1
  action_bound : (∫ τ in 0..T, b.dissipation τ) ≤ Real.exp (2 / (c.normalizedProduct t - 1)) - 1
  uniform : ∀ τ ∈ Icc 0 T,
    b.energy τ ∈ Icc 1 (Real.exp (2 / (c.normalizedProduct t - 1))) ∧
    b.length τ ∈ Icc (Real.exp (-(2 / (c.normalizedProduct t - 1))) *
      Real.sqrt (c.normalizedProduct t ^ 2 - c.normalizedProduct t)) (c.normalizedProduct t)
  flat_slice : ∃ τ ∈ Icc 0 T, ∀ u,
    (|curvature (b.position τ) u| / b.energy τ) ^ 6 ≤
      33554432 / (c.normalizedProduct t * (c.normalizedProduct t - 1))

theorem exists_rescaled_record_window (hflow : c.IsNormalFEF)
    (hunbounded : ¬ c.HasBoundedEnergyLength) {K : ℝ} (hK : c.normalizedProduct 0 + 2 ≤ K) :
    ∃ t, K ≤ c.normalizedProduct t ∧ ∃ (s T : ℝ) (b : ForwardImmersion), c.RescaledRecordWindow b s t T := by
  obtain ⟨t, ht, hKt, hrec, s, hs, hb, _, hz, hTlo, hThi, _, _, _⟩ :=
    c.exists_high_record_window_of_unbounded hflow hunbounded hK
  let r := c.energy t
  have hr : 0 < r := c.energy_pos ht
  have hr4 := pow_pos hr 4
  let T := r ^ 4 * (t - s)
  let b := c.rescaled r s hr hs.1
  have hf : b.IsNormalFEF := c.rescaled_isNormalFEF hflow r s hr hs.1
  have ha := c.high_record_budget_admissible hflow ht (hK.trans hKt)
  have hT : 0 < T := (mul_pos ha.1 (Real.exp_pos _)).trans_le hTlo
  have htime {τ : ℝ} (hτ : τ ∈ Icc 0 T) : s + τ / r ^ 4 ∈ Icc s t := by
    refine ⟨le_add_of_nonneg_right (div_nonneg hτ.1 hr4.le), ?_⟩
    have h := (div_le_iff₀ hr4).mpr (by simpa only [T, mul_comm] using hτ.2)
    linarith
  have hend : s + T / r ^ 4 = t := by dsimp [T]; field_simp [hr.ne']; ring
  have hE : b.energy T = 1 := by rw [c.rescaled_energy, hend, div_self hr.ne']
  have hL : b.length T = c.normalizedProduct t := by rw [c.rescaled_length, hend]; rfl
  have hE0 : b.energy 0 = Real.exp (c.relativeDissipation s t) := by
    rw [c.rescaled_energy, zero_div, add_zero]
    exact c.energy_ratio_eq_exp_relativeDissipation hflow hs.1 hs.2
  have hD := b.energy_add_integral_dissipation hf (s := 0) le_rfl hT.le
  rw [hE, hE0] at hD
  have hact : (∫ τ in 0..T, b.dissipation τ) = Real.exp (c.relativeDissipation s t) - 1 := by linarith
  refine ⟨t, hKt, s, T, b, hs, hrec, hb, hf, rfl, rfl, hT, ⟨hTlo, hThi⟩,
    fun _ _ => rfl, ?_, hE, hL, hact, ?_, ?_, ?_⟩
  · intro δ hδ
    have hin : T + δ ∈ Icc 0 T := ⟨by linarith [hδ.1], by linarith [hδ.2]⟩
    have he : s + (T + δ) / r ^ 4 = t + δ / r ^ 4 := by rw [add_div, ← add_assoc, hend]
    refine ⟨hin, he ▸ htime hin, fun u => ?_⟩
    change r • c.position (s + (T + δ) / r ^ 4) u = _
    rw [he]
  · rw [hact]
    exact sub_le_sub_right (Real.exp_le_exp.mpr hz) _
  · intro τ hτ
    have hx := htime hτ
    have hsmall : c.energyFourthBudget s t < c.normalizedProduct t ^ 2 := hb ▸ ha.2.2
    have hlen := c.terminal_scaled_length_lower_on_window hflow hs.1 hx hsmall
    rw [hb] at hlen
    have hen := c.energy_ratio_bounds_on_window hflow hs.1 hx
    rw [c.rescaled_energy, c.rescaled_length]
    exact ⟨⟨hen.1, hen.2.trans (Real.exp_le_exp.mpr hz)⟩,
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hz)) (Real.sqrt_nonneg _)).trans hlen,
      c.terminal_scaled_length_le_of_record hflow (hs.1.trans hx.1) hx.2
        (hrec _ ⟨hs.1.trans hx.1, hx.2⟩)⟩
  · obtain ⟨x, hx, hmin⟩ := c.exists_dissipation_slice hs.1 hs.2
    rw [hb] at hmin
    have hratio : c.dissipation x / c.energy x ^ 5 ≤ 2 / (c.normalizedProduct t * (c.normalizedProduct t - 1)) := by
      rw [mul_comm (c.normalizedProduct t), ← div_div]
      exact (le_div_iff₀ ha.1).mpr (hmin.trans hz)
    let τ := r ^ 4 * (x - s)
    have hin : τ ∈ Icc 0 T := ⟨mul_nonneg hr4.le (sub_nonneg.mpr hx.1),
      mul_le_mul_of_nonneg_left (sub_le_sub_right hx.2 s) hr4.le⟩
    have he : s + τ / r ^ 4 = x := by dsimp [τ]; field_simp [hr.ne']; ring
    refine ⟨τ, hin, fun u => ?_⟩
    have hd : b.dissipation τ / b.energy τ ^ 5 = c.dissipation x / c.energy x ^ 5 := by
      rw [c.rescaled_dissipation, c.rescaled_energy, he]
      field_simp [hr.ne', (c.energy_pos (hs.1.trans hx.1)).ne']
    have hl := b.normalized_curvature_six_le hin.1 u
    rw [hd] at hl
    calc
      _ ≤ _ := hl
      _ ≤ 16777216 * (2 / (c.normalizedProduct t * (c.normalizedProduct t - 1))) :=
        mul_le_mul_of_nonneg_left hratio (by norm_num)
      _ = _ := by ring

end LengthGrowth.ActualFlow.ForwardImmersion
