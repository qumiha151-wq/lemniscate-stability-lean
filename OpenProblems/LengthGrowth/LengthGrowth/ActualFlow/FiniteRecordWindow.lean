import LengthGrowth.ActualFlow.RelativeEnergy

/-! Finite physical-time record windows for actual forward normal FEF.
The budget start is obtained by the intermediate value theorem, without
constructing an energy-clock inverse. No infinite record sequence, ancient
limit, compactness, uniform curvature cap, or length bound is assumed. -/

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth.ActualFlow.ForwardImmersion

variable (c : ForwardImmersion)

def energyBudgetPrimitive (t : ℝ) : ℝ := c.energyFourthBudget 0 t

theorem energyBudgetPrimitive_zero : c.energyBudgetPrimitive 0 = 0 := by
  simp [energyBudgetPrimitive, energyFourthBudget]

theorem energyBudgetPrimitive_continuousOn :
    ContinuousOn c.energyBudgetPrimitive (Ici 0) := by
  -- Only the scalar integrand is continuously extended by clamping its
  -- argument. This is not a backward extension of the geometric flow.
  have hf : Continuous (fun x : ℝ => c.energy (max x 0) ^ 4) :=
    (c.energy_continuousOn.comp_continuous (continuous_id.max continuous_const)
      (fun x => le_max_right x 0)).pow 4
  have hp : Continuous (fun t : ℝ => ∫ x in 0..t, c.energy (max x 0) ^ 4) :=
    intervalIntegral.continuous_primitive
    (fun a b => hf.intervalIntegrable a b) 0
  apply hp.continuousOn.congr
  intro t ht
  change (∫ x in 0..t, c.energy x ^ 4) = ∫ x in 0..t, c.energy (max x 0) ^ 4
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le ht] at hx
  change c.energy x ^ 4 = c.energy (max x 0) ^ 4
  rw [max_eq_left hx.1]

theorem energyBudgetPrimitive_add {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    c.energyBudgetPrimitive s + c.energyFourthBudget s t = c.energyBudgetPrimitive t := by
  have h1 : Icc 0 s ⊆ Ici 0 := fun x hx => hx.1
  have h2 : Icc s t ⊆ Ici 0 := fun x hx => hs.trans hx.1
  exact intervalIntegral.integral_add_adjacent_intervals
    (((c.energy_continuousOn.pow 4).mono h1).intervalIntegrable_of_Icc hs)
    (((c.energy_continuousOn.pow 4).mono h2).intervalIntegrable_of_Icc hst)

theorem energyFourthBudget_pos {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    0 < c.energyFourthBudget s t := by
  have hsub : Icc s t ⊆ Ici 0 := fun x hx => hs.trans hx.1
  apply intervalIntegral.integral_pos hst ((c.energy_continuousOn.pow 4).mono hsub)
  · intro x _hx
    exact pow_nonneg (c.energy_nonneg x) 4
  · exact ⟨s, ⟨le_rfl, hst.le⟩, pow_pos (c.energy_pos hs) 4⟩

theorem energyBudgetPrimitive_strictMonoOn :
    StrictMonoOn c.energyBudgetPrimitive (Ici 0) := by
  intro s hs t _ht hst
  have ha := c.energyBudgetPrimitive_add hs hst.le
  have hp := c.energyFourthBudget_pos hs hst
  linarith

theorem energyFourthBudget_eq_zero_iff {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    c.energyFourthBudget s t = 0 ↔ s = t := by
  constructor
  · intro hz
    rcases eq_or_lt_of_le hst with he | he
    · exact he
    · have hp := c.energyFourthBudget_pos hs he
      linarith
  · rintro rfl
    simp [energyFourthBudget]

/-- Actual IVT selection on one finite interval, with uniqueness. -/
theorem exists_unique_energyBudget_start {t R : ℝ} (ht : 0 ≤ t)
    (hR : 0 ≤ R) (hRt : R ≤ c.energyBudgetPrimitive t) :
    ∃! s, s ∈ Icc 0 t ∧ c.energyFourthBudget s t = R := by
  have hc := c.energyBudgetPrimitive_continuousOn.mono
    (show Icc 0 t ⊆ Ici 0 from fun x hx => hx.1)
  have hy : c.energyBudgetPrimitive t - R ∈
      Icc (c.energyBudgetPrimitive 0) (c.energyBudgetPrimitive t) := by
    rw [c.energyBudgetPrimitive_zero]
    constructor <;> linarith
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc ht hc hy
  have ha := c.energyBudgetPrimitive_add hs.1 hs.2
  have hsR : c.energyFourthBudget s t = R := by linarith
  refine ⟨s, ⟨hs, hsR⟩, ?_⟩
  intro y hy
  have ha' := c.energyBudgetPrimitive_add hy.1.1 hy.1.2
  apply c.energyBudgetPrimitive_strictMonoOn.injOn hy.1.1 hs.1
  linarith [hy.2]

theorem energyBudget_start_eq_terminal_iff {s t R : ℝ}
    (hs : s ∈ Icc 0 t) (h : c.energyFourthBudget s t = R) : s = t ↔ R = 0 := by
  rw [← h, c.energyFourthBudget_eq_zero_iff hs.1 hs.2]

theorem energyBudget_start_eq_zero_iff {s t R : ℝ}
    (hs : s ∈ Icc 0 t) (h : c.energyFourthBudget s t = R) :
    s = 0 ↔ R = c.energyBudgetPrimitive t := by
  constructor
  · rintro rfl
    exact h.symm
  · intro hR
    apply c.energyBudgetPrimitive_strictMonoOn.injOn hs.1 (by simp)
    have ha := c.energyBudgetPrimitive_add hs.1 hs.2
    rw [c.energyBudgetPrimitive_zero]
    linarith

/-- Bounds on a selected actual window; whole-interval record assumptions
are unnecessary here because endpoint product gain suffices. -/
theorem selected_record_window_bounds (hflow : c.IsNormalFEF)
    {s t R : ℝ} (hs : s ∈ Icc 0 t) (hR : 0 ≤ R)
    (hbudget : c.energyFourthBudget s t = R)
    (hgain : c.normalizedProduct s ≤ c.normalizedProduct t)
    (hsmall : R < c.normalizedProduct t ^ 2) :
    0 ≤ c.relativeDissipation s t ∧
    c.relativeDissipation s t ≤ 2 * R / (c.normalizedProduct t ^ 2 - R) ∧
    R * Real.exp (-8 * R / (c.normalizedProduct t ^ 2 - R)) ≤
      c.energy t ^ 4 * (t - s) ∧
    c.energy t ^ 4 * (t - s) ≤ R ∧
    1 ≤ c.energy s / c.energy t ∧
    c.energy s / c.energy t ≤ Real.exp (2 * R / (c.normalizedProduct t ^ 2 - R)) ∧
    (∫ x in s..t, c.dissipation x) / c.energy t ≤
      Real.exp (2 * R / (c.normalizedProduct t ^ 2 - R)) - 1 := by
  have hb : c.energyFourthBudget s t < c.normalizedProduct t ^ 2 := by rwa [hbudget]
  have hz := c.relativeDissipation_le_of_product_gain hflow hs.1 hs.2 hgain hb
  rw [hbudget] at hz
  have ht := c.endpoint_energy_fourth_window_bounds hflow hs.1 hs.2
  rw [hbudget] at ht
  have hr := c.energy_ratio_eq_exp_relativeDissipation hflow hs.1 hs.2
  have he := c.energy_le_of_le hflow hs.1 hs.2
  have hpos := c.energy_pos (hs.1.trans hs.2)
  have hex : -8 * R / (c.normalizedProduct t ^ 2 - R) ≤
      -4 * c.relativeDissipation s t := by
    have hid : -8 * R / (c.normalizedProduct t ^ 2 - R) =
        -4 * (2 * R / (c.normalizedProduct t ^ 2 - R)) := by ring
    rw [hid]
    linarith
  have hrat : c.energy s / c.energy t ≤
      Real.exp (2 * R / (c.normalizedProduct t ^ 2 - R)) := by
    rw [hr]
    exact Real.exp_le_exp.mpr hz
  refine ⟨c.relativeDissipation_nonneg hs.2, hz,
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex) hR).trans ht.1,
    ht.2, ?_, hrat, ?_⟩
  · apply (le_div_iff₀ hpos).mpr
    simpa only [one_mul] using he
  · have hd := c.energy_add_integral_dissipation hflow hs.1 hs.2
    have hd' : (∫ x in s..t, c.dissipation x) = c.energy s - c.energy t := by linarith
    rw [hd', c.relative_energy_loss_eq_exp_sub_one hflow hs.1 hs.2]
    exact sub_le_sub_right (Real.exp_le_exp.mpr hz) 1

/-- A finite record hypothesis permits IVT selection with all quantitative
bounds, including R=0. No unbounded sequence of records is asserted. -/
theorem exists_finite_record_window (hflow : c.IsNormalFEF)
    {t R : ℝ} (ht : 0 ≤ t) (hR : 0 ≤ R) (hRt : R ≤ c.energyBudgetPrimitive t)
    (hsmall : R < c.normalizedProduct t ^ 2)
    (hrecord : ∀ x ∈ Icc 0 t, c.normalizedProduct x ≤ c.normalizedProduct t) :
    ∃ s, s ∈ Icc 0 t ∧ c.energyFourthBudget s t = R ∧
      0 ≤ c.relativeDissipation s t ∧
      c.relativeDissipation s t ≤ 2 * R / (c.normalizedProduct t ^ 2 - R) ∧
      R * Real.exp (-8 * R / (c.normalizedProduct t ^ 2 - R)) ≤
        c.energy t ^ 4 * (t - s) ∧
      c.energy t ^ 4 * (t - s) ≤ R ∧
      1 ≤ c.energy s / c.energy t ∧
      c.energy s / c.energy t ≤ Real.exp (2 * R / (c.normalizedProduct t ^ 2 - R)) ∧
      (∫ x in s..t, c.dissipation x) / c.energy t ≤
        Real.exp (2 * R / (c.normalizedProduct t ^ 2 - R)) - 1 := by
  obtain ⟨s, hs, _hu⟩ := c.exists_unique_energyBudget_start ht hR hRt
  exact ⟨s, hs.1, hs.2, c.selected_record_window_bounds hflow hs.1 hR hs.2
    (hrecord s hs.1) hsmall⟩

/-- A concrete finite threshold makes R=e(t) an admissible budget. -/
theorem high_record_budget_admissible (hflow : c.IsNormalFEF) {t : ℝ} (ht : 0 ≤ t)
    (hhigh : c.normalizedProduct 0 + 2 ≤ c.normalizedProduct t) :
    0 < c.normalizedProduct t ∧
    c.normalizedProduct t ≤ c.energyBudgetPrimitive t ∧
    c.normalizedProduct t < c.normalizedProduct t ^ 2 := by
  have hn := c.normalizedProduct_nonneg 0
  have hu := c.normalizedProduct_sq_sub_le_integral_energy_fourth hflow (s := 0) (by rfl) ht
  change _ ≤ c.energyBudgetPrimitive t at hu
  have hdiff : c.normalizedProduct 0 + 2 ≤ c.normalizedProduct t := hhigh
  have hsq := sq_nonneg (c.normalizedProduct t - (c.normalizedProduct 0 + 2))
  constructor
  · linarith
  constructor <;> nlinarith

/-- At a finite high record, choose R=e(t) and simplify every quantitative
constant. This asserts no existence of high records along an arbitrary flow. -/
theorem exists_high_record_window (hflow : c.IsNormalFEF)
    {t : ℝ} (ht : 0 ≤ t)
    (hhigh : c.normalizedProduct 0 + 2 ≤ c.normalizedProduct t)
    (hrecord : ∀ x ∈ Icc 0 t, c.normalizedProduct x ≤ c.normalizedProduct t) :
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
  have ha := c.high_record_budget_admissible hflow ht hhigh
  have h1 : 1 < c.normalizedProduct t := by
    have hn := c.normalizedProduct_nonneg 0
    linarith
  have hcancel (a : ℝ) : a * c.normalizedProduct t /
      (c.normalizedProduct t ^ 2 - c.normalizedProduct t) = a / (c.normalizedProduct t - 1) := by
    rw [show c.normalizedProduct t ^ 2 - c.normalizedProduct t =
      c.normalizedProduct t * (c.normalizedProduct t - 1) by ring]
    field_simp [ne_of_gt ha.1, ne_of_gt (sub_pos.mpr h1)]
  simpa only [hcancel] using c.exists_finite_record_window hflow ht ha.1.le
    ha.2.1 ha.2.2 hrecord

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
  logInfo m!"Actual finite record window: {count} declarations; standard axioms only."
