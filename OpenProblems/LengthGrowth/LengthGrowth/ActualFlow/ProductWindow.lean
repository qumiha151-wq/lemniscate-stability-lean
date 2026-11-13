import LengthGrowth.ActualFlow.NormalizedProduct
import LengthGrowth.ActualFlow.ArclengthCoercivity

/-! A physical-time window estimate for genuine forward normal FEF.
All quantities are the actual material integrals of the position family.
Only endpoint product gain is assumed; no record maximum or clock inverse
is used. Initial time is included by continuity and interior-only FTC. -/

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth

/-- The quadratic proof of interval Cauchy--Schwarz uses continuity only on
the relevant compact interval, not on negative physical times. -/
theorem interval_integral_mul_sq_le_continuousOn {f g : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b)) (hab : a ≤ b) :
    (∫ s in a..b, f s * g s) ^ 2 ≤
      (∫ s in a..b, f s ^ 2) * (∫ s in a..b, g s ^ 2) := by
  let A := ∫ s in a..b, f s ^ 2
  let B := ∫ s in a..b, f s * g s
  let C := ∫ s in a..b, g s ^ 2
  have hpoly : ∀ t : ℝ, 0 ≤ C * (t * t) + (2 * B) * t + A := by
    intro t
    have hpos : 0 ≤ ∫ s in a..b, (f s + t * g s) ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall hab (fun s => sq_nonneg _)
    have heq : (fun s => (f s + t * g s) ^ 2) =
        (fun s => f s ^ 2 + (2 * t) * (f s * g s) + (t * t) * (g s ^ 2)) := by
      funext s
      ring
    rw [heq, intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hpos
    · dsimp [A, B, C]
      nlinarith
    · exact (hf.pow 2).intervalIntegrable_of_Icc hab
    · exact ((hf.mul hg).const_mul (2 * t)).intervalIntegrable_of_Icc hab
    · exact ((hf.pow 2).add ((hf.mul hg).const_mul (2 * t))).intervalIntegrable_of_Icc hab
    · exact ((hg.pow 2).const_mul (t * t)).intervalIntegrable_of_Icc hab
  have hdisc := discrim_le_zero hpoly
  dsimp [discrim] at hdisc
  change B ^ 2 ≤ A * C
  nlinarith

namespace ActualFlow.ForwardImmersion

variable (c : ForwardImmersion)

def energyFourthBudget (s t : ℝ) : ℝ := ∫ x in s..t, c.energy x ^ 4

def relativeDissipation (s t : ℝ) : ℝ := ∫ x in s..t, c.dissipation x / c.energy x

theorem relativeDissipation_density_continuousOn :
    ContinuousOn (fun x => c.dissipation x / c.energy x) (Ici 0) :=
  c.dissipation_continuousOn.div c.energy_continuousOn
    (fun _x hx => ne_of_gt (c.energy_pos hx))

theorem energyFourthBudget_nonneg {s t : ℝ} (hst : s ≤ t) :
    0 ≤ c.energyFourthBudget s t :=
  intervalIntegral.integral_nonneg_of_forall hst (fun x => pow_nonneg (c.energy_nonneg x) 4)

theorem relativeDissipation_nonneg {s t : ℝ} (hst : s ≤ t) :
    0 ≤ c.relativeDissipation s t :=
  intervalIntegral.integral_nonneg_of_forall hst
    (fun x => div_nonneg (c.dissipation_nonneg x) (c.energy_nonneg x))

theorem normalizedProduct_nonneg (t : ℝ) : 0 ≤ c.normalizedProduct t :=
  mul_nonneg (c.energy_nonneg t) (c.length_nonneg t)

/-- The terminal product and the physical energy budget give a lower bound
throughout the window, without assuming a first-record property. -/
theorem normalizedProduct_lower_on_window (hflow : c.IsNormalFEF)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hb : c.energyFourthBudget s t < c.normalizedProduct t ^ 2)
    {x : ℝ} (hx : x ∈ Icc s t) :
    Real.sqrt (c.normalizedProduct t ^ 2 - c.energyFourthBudget s t) ≤
      c.normalizedProduct x := by
  have hsub : Icc s t ⊆ Ici 0 := fun y hy => hs.trans hy.1
  have hi : IntervalIntegrable (fun x => c.energy x ^ 4) volume s t :=
    ((c.energy_continuousOn.pow 4).mono hsub).intervalIntegrable_of_Icc hst
  have hmono : (∫ y in x..t, c.energy y ^ 4) ≤ c.energyFourthBudget s t :=
    intervalIntegral.integral_mono_interval hx.1 hx.2 le_rfl
      (Filter.Eventually.of_forall (fun y => pow_nonneg (c.energy_nonneg y) 4)) hi
  have h := c.normalizedProduct_sq_sub_le_integral_energy_fourth hflow (hsub hx) hx.2
  have hr := Real.sq_sqrt (sub_nonneg.mpr hb.le)
  have he := c.normalizedProduct_nonneg x
  nlinarith [Real.sqrt_nonneg (c.normalizedProduct t ^ 2 - c.energyFourthBudget s t)]

theorem normalizedProduct_sub_eq_integral_rate (hflow : c.IsNormalFEF)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    c.normalizedProduct t - c.normalizedProduct s =
      (∫ x in s..t, c.energy x * c.lengthRate x) -
        ∫ x in s..t, c.length x * c.dissipation x := by
  have hsub : Icc s t ⊆ Ici 0 := fun x hx => hs.trans hx.1
  have hA : ContinuousOn (fun x => c.energy x * c.lengthRate x) (Icc s t) :=
    (c.energy_continuousOn.mul c.lengthRate_continuousOn).mono hsub
  have hB : ContinuousOn (fun x => c.length x * c.dissipation x) (Icc s t) :=
    (c.length_continuousOn.mul c.dissipation_continuousOn).mono hsub
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst
    (c.normalizedProduct_continuousOn.mono hsub)
    (fun x hx => c.normalizedProduct_hasDerivAt_normal hflow (lt_of_le_of_lt hs hx.1))
    ((hA.sub hB).intervalIntegrable_of_Icc hst)
  rw [intervalIntegral.integral_sub (hA.intervalIntegrable_of_Icc hst)
    (hB.intervalIntegrable_of_Icc hst)] at he
  exact he.symm

/-- Actual weighted Cauchy--Schwarz on one nonnegative physical-time window. -/
theorem energy_lengthRate_integral_sq_le {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (∫ x in s..t, c.energy x * c.lengthRate x) ^ 2 ≤
      2 * c.energyFourthBudget s t * c.relativeDissipation s t := by
  have hsub : Icc s t ⊆ Ici 0 := fun x hx => hs.trans hx.1
  have hE := c.energy_continuousOn.mono hsub
  have hL := c.lengthRate_continuousOn.mono hsub
  have hquot : ContinuousOn (fun x => c.lengthRate x / c.energy x) (Icc s t) :=
    hL.div hE (fun x hx => ne_of_gt (c.energy_pos (hsub hx)))
  have hcs := interval_integral_mul_sq_le_continuousOn (hE.pow 2) hquot hst
  simp only [Pi.pow_apply] at hcs
  have heq : (∫ x in s..t, c.energy x ^ 2 * (c.lengthRate x / c.energy x)) =
      ∫ x in s..t, c.energy x * c.lengthRate x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hst] at hx
    have hn := ne_of_gt (c.energy_pos (hs.trans hx.1))
    field_simp [hn]
  have heq4 : (fun x => (c.energy x ^ 2) ^ 2) = (fun x => c.energy x ^ 4) := by
    funext x
    ring
  rw [heq, heq4] at hcs
  have hratio : (∫ x in s..t, (c.lengthRate x / c.energy x) ^ 2) ≤
      2 * c.relativeDissipation s t := by
    have hd := c.relativeDissipation_density_continuousOn.mono hsub
    calc
      (∫ x in s..t, (c.lengthRate x / c.energy x) ^ 2) ≤
          ∫ x in s..t, 2 * (c.dissipation x / c.energy x) := by
        apply intervalIntegral.integral_mono_on hst
          ((hquot.pow 2).intervalIntegrable_of_Icc hst)
          ((hd.const_mul 2).intervalIntegrable_of_Icc hst)
        intro x hx
        have hp := c.energy_pos (hsub hx)
        have hb := c.lengthRate_sq_le (hsub hx)
        convert! (div_le_div_of_nonneg_right hb (sq_nonneg (c.energy x))) using 1
        · exact div_pow _ _ 2
        · field_simp [ne_of_gt hp]
      _ = 2 * c.relativeDissipation s t := intervalIntegral.integral_const_mul _ _
  change _ ≤ c.energyFourthBudget s t * _ at hcs
  have hm := mul_le_mul_of_nonneg_left hratio (c.energyFourthBudget_nonneg hst)
  nlinarith

/-- If the endpoint product gains and the physical fourth-energy budget is
smaller than the terminal product squared, relative dissipation is small. -/
theorem productWindow_bound (hflow : c.IsNormalFEF)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hgain : c.normalizedProduct s ≤ c.normalizedProduct t)
    (hb : c.energyFourthBudget s t < c.normalizedProduct t ^ 2) :
    (c.normalizedProduct t ^ 2 - c.energyFourthBudget s t) *
      c.relativeDissipation s t ≤ 2 * c.energyFourthBudget s t := by
  let m := Real.sqrt (c.normalizedProduct t ^ 2 - c.energyFourthBudget s t)
  have hm : 0 ≤ m := Real.sqrt_nonneg _
  have hm2 : m ^ 2 = c.normalizedProduct t ^ 2 - c.energyFourthBudget s t :=
    Real.sq_sqrt (sub_nonneg.mpr hb.le)
  have hZ := c.relativeDissipation_nonneg hst
  have hsub : Icc s t ⊆ Ici 0 := fun x hx => hs.trans hx.1
  have hload : m * c.relativeDissipation s t ≤
      ∫ x in s..t, c.length x * c.dissipation x := by
    rw [relativeDissipation, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hst
      (((c.relativeDissipation_density_continuousOn.mono hsub).const_mul m).intervalIntegrable_of_Icc hst)
      (((c.length_continuousOn.mul c.dissipation_continuousOn).mono hsub).intervalIntegrable_of_Icc hst)
    intro x hx
    have hmE := c.normalizedProduct_lower_on_window hflow hs hst hb hx
    have hD := div_nonneg (c.dissipation_nonneg x) (c.energy_nonneg x)
    have hmul := mul_le_mul_of_nonneg_right hmE hD
    have hn := ne_of_gt (c.energy_pos (hsub hx))
    convert! hmul using 1
    dsimp [normalizedProduct]
    field_simp [hn]
  have hg := c.normalizedProduct_sub_eq_integral_rate hflow hs hst
  have hload2 : m * c.relativeDissipation s t ≤
      ∫ x in s..t, c.energy x * c.lengthRate x := by linarith
  have hI : 0 ≤ ∫ x in s..t, c.energy x * c.lengthRate x :=
    (mul_nonneg hm hZ).trans hload2
  have hsq := c.energy_lengthRate_integral_sq_le hs hst
  have hloadsq : (m * c.relativeDissipation s t) ^ 2 ≤
      (∫ x in s..t, c.energy x * c.lengthRate x) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hm hZ) hload2 2
  rcases eq_or_lt_of_le hZ with hz | hz
  · rw [← hz, mul_zero]
    exact mul_nonneg (by norm_num) (c.energyFourthBudget_nonneg hst)
  · have hh : (m ^ 2 * c.relativeDissipation s t) * c.relativeDissipation s t ≤
        (2 * c.energyFourthBudget s t) * c.relativeDissipation s t := by
      nlinarith
    have hh' := (mul_le_mul_iff_of_pos_right hz).mp hh
    nlinarith [hm2]

theorem relativeDissipation_le_of_product_gain (hflow : c.IsNormalFEF)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hgain : c.normalizedProduct s ≤ c.normalizedProduct t)
    (hb : c.energyFourthBudget s t < c.normalizedProduct t ^ 2) :
    c.relativeDissipation s t ≤ 2 * c.energyFourthBudget s t /
      (c.normalizedProduct t ^ 2 - c.energyFourthBudget s t) := by
  apply (le_div_iff₀ (sub_pos.mpr hb)).mpr
  simpa only [mul_comm] using c.productWindow_bound hflow hs hst hgain hb

end ActualFlow.ForwardImmersion
end LengthGrowth

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (n, _) in (← getEnv).constants do
    if (`LengthGrowth).isPrefixOf n || (`FreeElasticScalar).isPrefixOf n then
      for a in (← collectAxioms n) do
        unless allowed.contains a do throwError "Unexpected axiom {a} in {n}"
      count := count + 1
  logInfo m!"Actual product window: {count} declarations; standard axioms only."
