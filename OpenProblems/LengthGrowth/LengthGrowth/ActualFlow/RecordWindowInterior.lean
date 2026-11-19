import LengthGrowth.ActualFlow.FiniteRecordWindow

/-! Uniform estimates on an actual finite physical-time window.
The terminal energy is frozen as a constant spatial scale. These identities
refer to the existing flow's actual integrals; a rescaled curve constructor
is supplied separately. No ancient limit or bounded product is asserted. -/

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth.ActualFlow.ForwardImmersion

variable (c : ForwardImmersion)

theorem energy_ratio_bounds_on_window (hflow : c.IsNormalFEF)
    {s t x : ℝ} (hs : 0 ≤ s) (hx : x ∈ Icc s t) :
    1 ≤ c.energy x / c.energy t ∧
      c.energy x / c.energy t ≤ Real.exp (c.relativeDissipation s t) := by
  have ht := hs.trans (hx.1.trans hx.2)
  have hp := c.energy_pos ht
  constructor
  · apply (le_div_iff₀ hp).mpr
    simpa only [one_mul] using c.energy_le_of_le hflow (hs.trans hx.1) hx.2
  · rw [← c.energy_ratio_eq_exp_relativeDissipation hflow hs (hx.1.trans hx.2)]
    exact div_le_div_of_nonneg_right (c.energy_le_of_le hflow hs hx.1) hp.le

/-- The frozen terminal scale gives a lower length bound everywhere in the
window, even without a record assumption. -/
theorem terminal_scaled_length_lower_on_window (hflow : c.IsNormalFEF)
    {s t x : ℝ} (hs : 0 ≤ s) (hx : x ∈ Icc s t)
    (hb : c.energyFourthBudget s t < c.normalizedProduct t ^ 2) :
    Real.exp (-c.relativeDissipation s t) *
        Real.sqrt (c.normalizedProduct t ^ 2 - c.energyFourthBudget s t) ≤
      c.energy t * c.length x := by
  have hst := hx.1.trans hx.2
  have hlow := c.normalizedProduct_lower_on_window hflow hs hst hb hx
  have he := c.energy_le_of_le hflow hs hx.1
  have hex : Real.exp (-c.relativeDissipation s t) *
      Real.exp (c.relativeDissipation s t) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    Real.exp (-c.relativeDissipation s t) *
        Real.sqrt (c.normalizedProduct t ^ 2 - c.energyFourthBudget s t) ≤
        Real.exp (-c.relativeDissipation s t) * c.normalizedProduct x :=
      mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le
    _ = Real.exp (-c.relativeDissipation s t) * c.energy x * c.length x := by
      simp only [normalizedProduct, mul_assoc]
    _ ≤ Real.exp (-c.relativeDissipation s t) * c.energy s * c.length x :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le) (c.length_nonneg x)
    _ = c.energy t * c.length x := by
      rw [c.energy_eq_terminal_mul_exp_relativeDissipation hflow hs hst]
      calc
        _ = (Real.exp (-c.relativeDissipation s t) *
            Real.exp (c.relativeDissipation s t)) * (c.energy t * c.length x) := by ring
        _ = _ := by rw [hex, one_mul]

theorem terminal_scaled_length_le_of_record (hflow : c.IsNormalFEF)
    {x t : ℝ} (hx : 0 ≤ x) (hxt : x ≤ t)
    (hrecord : c.normalizedProduct x ≤ c.normalizedProduct t) :
    c.energy t * c.length x ≤ c.normalizedProduct t := by
  calc
    c.energy t * c.length x ≤ c.energy x * c.length x :=
      mul_le_mul_of_nonneg_right (c.energy_le_of_le hflow hx hxt) (c.length_nonneg x)
    _ ≤ c.normalizedProduct t := hrecord

/-- Explicit estimates hold at every point of a finite record window.
The constants depend only on its actual terminal product and energy budget. -/
theorem finite_record_window_uniform_bounds (hflow : c.IsNormalFEF)
    {s t R : ℝ} (hs : s ∈ Icc 0 t)
    (hbudget : c.energyFourthBudget s t = R)
    (hsmall : R < c.normalizedProduct t ^ 2)
    (hrecord : ∀ x ∈ Icc 0 t, c.normalizedProduct x ≤ c.normalizedProduct t)
    {x : ℝ} (hx : x ∈ Icc s t) :
    Real.sqrt (c.normalizedProduct t ^ 2 - R) ≤ c.normalizedProduct x ∧
    c.normalizedProduct x ≤ c.normalizedProduct t ∧
    1 ≤ c.energy x / c.energy t ∧
    c.energy x / c.energy t ≤ Real.exp (2 * R / (c.normalizedProduct t ^ 2 - R)) ∧
    Real.exp (-(2 * R / (c.normalizedProduct t ^ 2 - R))) *
        Real.sqrt (c.normalizedProduct t ^ 2 - R) ≤ c.energy t * c.length x ∧
    c.energy t * c.length x ≤ c.normalizedProduct t := by
  have hb : c.energyFourthBudget s t < c.normalizedProduct t ^ 2 := by rwa [hbudget]
  have hrec := hrecord x ⟨hs.1.trans hx.1, hx.2⟩
  have hz := c.relativeDissipation_le_of_product_gain hflow hs.1 hs.2 (hrecord s hs) hb
  have hlow := c.normalizedProduct_lower_on_window hflow hs.1 hs.2 hb hx
  have hlen := c.terminal_scaled_length_lower_on_window hflow hs.1 hx hb
  rw [hbudget] at hz hlow hlen
  have he := c.energy_ratio_bounds_on_window hflow hs.1 hx
  refine ⟨hlow, hrec, he.1, he.2.trans (Real.exp_le_exp.mpr hz), ?_,
    c.terminal_scaled_length_le_of_record hflow (hs.1.trans hx.1) hx.2 hrec⟩
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hz))
    (Real.sqrt_nonneg _)).trans hlen

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
  logInfo m!"Actual record window interior: {count} declarations; standard axioms only."
