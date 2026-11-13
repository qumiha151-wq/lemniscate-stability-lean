import LengthGrowth.ActualFlow.ForwardDissipation

/-! The actual energy-length product of a forward normal free elastic flow.
The square estimate is the physical-time version of the energy-normalized
identity in LengthEnergyNormalizedAncientWindows, Section 2. No energy clock,
positive-energy premise, monotone-length premise, or ancient limit is used. -/

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth.ActualFlow.ForwardImmersion

variable (c : ForwardImmersion)

/-- Product of the actual bending energy and actual material length. -/
def normalizedProduct (t : ℝ) : ℝ := c.energy t * c.length t

theorem normalizedProduct_continuousOn : ContinuousOn c.normalizedProduct (Ici 0) :=
  c.energy_continuousOn.mul c.length_continuousOn

theorem normalizedProduct_hasDerivAt_normal (hflow : c.IsNormalFEF)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt c.normalizedProduct
      (c.energy t * c.lengthRate t - c.length t * c.dissipation t) t := by
  have hd := (c.energy_hasDerivAt_normal hflow ht).mul
    (c.length_hasDerivAt_normal hflow ht)
  change HasDerivAt c.normalizedProduct _ t at hd
  convert! hd using 1
  ring

theorem normalizedProduct_sq_hasDerivAt_normal (hflow : c.IsNormalFEF)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => c.normalizedProduct x ^ 2)
      (2 * c.energy t * c.length t *
        (c.energy t * c.lengthRate t - c.length t * c.dissipation t)) t := by
  have hd := (c.normalizedProduct_hasDerivAt_normal hflow ht).pow 2
  change HasDerivAt (fun x => c.normalizedProduct x ^ 2) _ t at hd
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at hd
  convert! hd using 1
  simp only [normalizedProduct]
  ring

/-- The entire deficit is a square plus the actual weighted Cauchy--Schwarz
deficit. Its proof does not divide by energy, length, or dissipation. -/
theorem normalizedProduct_sq_rate_deficit (t : ℝ) :
    c.energy t ^ 4 -
        2 * c.energy t * c.length t *
          (c.energy t * c.lengthRate t - c.length t * c.dissipation t) =
      (c.energy t ^ 2 - c.length t * c.lengthRate t) ^ 2 +
        c.length t ^ 2 * (2 * c.energy t * c.dissipation t - c.lengthRate t ^ 2) := by
  ring

theorem normalizedProduct_sq_rate_le_energy_fourth {t : ℝ} (ht : 0 ≤ t) :
    2 * c.energy t * c.length t *
        (c.energy t * c.lengthRate t - c.length t * c.dissipation t) ≤
      c.energy t ^ 4 := by
  apply sub_nonneg.mp
  rw [c.normalizedProduct_sq_rate_deficit]
  exact add_nonneg (sq_nonneg _)
    (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (c.lengthRate_sq_le ht)))

theorem normalizedProduct_sq_deriv_le_energy_fourth (hflow : c.IsNormalFEF)
    {t : ℝ} (ht : 0 < t) :
    deriv (fun x => c.normalizedProduct x ^ 2) t ≤ c.energy t ^ 4 := by
  rw [(c.normalizedProduct_sq_hasDerivAt_normal hflow ht).deriv]
  exact c.normalizedProduct_sq_rate_le_energy_fourth ht.le

/-- Initial-inclusive integral estimate for the actual product. FTC uses
normal FEF only at strictly positive interior times, never at negative time. -/
theorem normalizedProduct_sq_sub_le_integral_energy_fourth (hflow : c.IsNormalFEF)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    c.normalizedProduct t ^ 2 - c.normalizedProduct s ^ 2 ≤
      ∫ x in s..t, c.energy x ^ 4 := by
  have hsub : Icc s t ⊆ Ici 0 := fun x hx => hs.trans hx.1
  have hc : ContinuousOn (fun x => 2 * c.energy x * c.length x *
      (c.energy x * c.lengthRate x - c.length x * c.dissipation x)) (Ici 0) :=
    ((c.energy_continuousOn.const_mul 2).mul c.length_continuousOn).mul
      ((c.energy_continuousOn.mul c.lengthRate_continuousOn).sub
        (c.length_continuousOn.mul c.dissipation_continuousOn))
  have hi : IntervalIntegrable (fun x => 2 * c.energy x * c.length x *
      (c.energy x * c.lengthRate x - c.length x * c.dissipation x)) volume s t :=
    (hc.mono hsub).intervalIntegrable_of_Icc hst
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst
    ((c.normalizedProduct_continuousOn.pow 2).mono hsub)
    (fun x hx => c.normalizedProduct_sq_hasDerivAt_normal hflow
      (lt_of_le_of_lt hs hx.1)) hi
  simp only [Pi.pow_apply] at he
  rw [← he]
  apply intervalIntegral.integral_mono_on hst hi
    (((c.energy_continuousOn.pow 4).mono hsub).intervalIntegrable_of_Icc hst)
  intro x hx
  exact c.normalizedProduct_sq_rate_le_energy_fourth (hsub hx)

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
  logInfo m!"Actual normalized product: {count} declarations, standard axioms only."
