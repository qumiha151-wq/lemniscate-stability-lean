import LengthGrowth.ActualFlow.ArclengthCoercivity
import LengthGrowth.ActualFlow.ForwardDissipation
import LengthGrowth.WeightedLengthComparison

/-! CONDITIONAL quarter-power growth of an actual forward normal FEF.
The additional premise is a uniform bound for the ACTUAL total absolute
curvature. It is not proved here. All scalar derivative/coercivity premises
are discharged from the checked geometric development. -/

noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth.ActualFlow

def capDissipationCoefficient (A0 : ℝ) : ℝ := 1 / (262144 * A0 ^ 6)

def capEnergyConstant (A0 : ℝ) : ℝ := 16 * A0 * Real.sqrt A0

theorem capEnergyConstant_pos {A0 : ℝ} (hA0 : 0 < A0) : 0 < capEnergyConstant A0 := by
  unfold capEnergyConstant
  positivity

theorem capEnergyConstant_pow_four {A0 : ℝ} (hA0 : 0 ≤ A0) :
    capEnergyConstant A0 ^ 4 = 65536 * A0 ^ 6 := by
  calc
    capEnergyConstant A0 ^ 4 = 65536 * A0 ^ 4 * (Real.sqrt A0 ^ 2) ^ 2 := by
      unfold capEnergyConstant
      ring
    _ = 65536 * A0 ^ 6 := by rw [Real.sq_sqrt hA0]; ring

theorem capDissipationCoefficient_pos {A0 : ℝ} (hA0 : 0 < A0) :
    0 < capDissipationCoefficient A0 := by
  unfold capDissipationCoefficient
  positivity

theorem cap_coefficient_budget {A0 : ℝ} (hA0 : 0 < A0) :
    4 * capDissipationCoefficient A0 * capEnergyConstant A0 ^ 4 = 1 := by
  rw [capEnergyConstant_pow_four hA0.le]
  unfold capDissipationCoefficient
  field_simp [ne_of_gt hA0]
  norm_num

namespace ForwardImmersion

variable (c : ForwardImmersion)

theorem absoluteCurvature_cap_pos {A0 : ℝ}
    (hA : ∀ s, 0 ≤ s → c.absoluteCurvature s ≤ A0) : 0 < A0 := by
  have hlow := c.absoluteCurvature_lower (t := 0) (by rfl)
  have hu := hA 0 (by rfl)
  linarith

theorem uniform_energy_coercivity_of_absoluteCurvature_cap {A0 : ℝ}
    (hA : ∀ s, 0 ≤ s → c.absoluteCurvature s ≤ A0) {t : ℝ} (ht : 0 ≤ t) :
    capDissipationCoefficient A0 * c.energy t ^ 5 ≤ c.dissipation t := by
  have hAt : 0 < c.absoluteCurvature t := lt_of_lt_of_le (by norm_num)
    (c.absoluteCurvature_lower ht)
  have hA0 := c.absoluteCurvature_cap_pos hA
  have hp := pow_le_pow_left₀ hAt.le (hA t ht) 6
  have hnum : 0 ≤ (1 / 262144 : ℝ) * c.energy t ^ 5 := by
    have he := c.energy_pos ht
    positivity
  have hd := (div_le_div_of_nonneg_left hnum (pow_pos hAt 6) hp).trans
    (c.absolute_curvature_coercivity ht)
  convert! hd using 1
  unfold capDissipationCoefficient
  field_simp [ne_of_gt hA0]

theorem conditional_energy_decay (hflow : c.IsNormalFEF) {A0 : ℝ}
    (hA : ∀ s, 0 ≤ s → c.absoluteCurvature s ≤ A0) {t : ℝ} (ht : 0 ≤ t) :
    c.energy t ≤ 1 / FreeElasticScalar.fourthRoot
      ((c.energy 0)⁻¹ ^ 4 + 4 * capDissipationCoefficient A0 * t) := by
  apply FreeElasticScalar.energy_le_fourthRoot_inverse c.energy c.dissipation
    (capDissipationCoefficient A0)
    (capDissipationCoefficient_pos (c.absoluteCurvature_cap_pos hA))
    c.energy_continuousOn (fun s hs => c.energy_pos hs)
    (fun s hs => c.energy_hasDerivAt_normal hflow hs) ?_ t ht
  intro s hs
  exact c.uniform_energy_coercivity_of_absoluteCurvature_cap hA hs.le

theorem conditional_weighted_quarter_bound (hflow : c.IsNormalFEF) {A0 : ℝ}
    (hA : ∀ s, 0 ≤ s → c.absoluteCurvature s ≤ A0) {t : ℝ} (ht : 0 ≤ t) :
    c.length t + Real.sqrt t * c.energy t ≤
      c.length 0 + 64 * A0 * Real.sqrt A0 * FreeElasticScalar.fourthRoot t := by
  have hA0 := c.absoluteCurvature_cap_pos hA
  have h := FreeElasticScalar.coercive_quarter_length_bound
    c.length c.energy c.lengthRate c.dissipation
    (capDissipationCoefficient A0) (capEnergyConstant A0)
    (capDissipationCoefficient_pos hA0) (capEnergyConstant_pos hA0)
    (le_of_eq (cap_coefficient_budget hA0).symm)
    c.length_continuousOn c.energy_continuousOn (fun s hs => c.energy_pos hs)
    (fun s hs => c.length_hasDerivAt_normal hflow hs)
    (fun s hs => c.energy_hasDerivAt_normal hflow hs)
    (fun s hs => c.lengthRate_sq_le hs.le)
    (fun s hs => c.uniform_energy_coercivity_of_absoluteCurvature_cap hA hs.le) t ht
  convert! h using 1
  unfold capEnergyConstant
  ring

theorem conditional_quarter_increment (hflow : c.IsNormalFEF) {A0 : ℝ}
    (hA : ∀ s, 0 ≤ s → c.absoluteCurvature s ≤ A0) {t : ℝ} (ht : 0 ≤ t) :
    c.length t - c.length 0 ≤
      64 * A0 * Real.sqrt A0 * FreeElasticScalar.fourthRoot t := by
  have h := c.conditional_weighted_quarter_bound hflow hA ht
  have he := mul_nonneg (Real.sqrt_nonneg t) (c.energy_pos ht).le
  linarith

end ForwardImmersion
end LengthGrowth.ActualFlow

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`LengthGrowth).isPrefixOf name || (`FreeElasticScalar).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext, `Classical.choice, `Quot.sound] : Array Name).contains axiomName do
          throwError "Conditional actual quarter-growth audit failed: {name} depends on {axiomName}"
      count := count + 1
  logInfo m!"CONDITIONAL_ACTUAL_QUARTER_GROWTH_AUDIT {count}: standard three axioms only."
