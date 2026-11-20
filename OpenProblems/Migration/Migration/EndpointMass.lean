import Migration.LocalizedFirstVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Each of the two parameter arcs between two material points pays the
change of a primitive of the height cutoff. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow

private theorem weightedArcCost (γ : ℝ → ℂ) (hγ : ContDiff ℝ ∞ γ)
    (H : ℂ →L[ℝ] ℝ) (hH : ‖H‖ ≤ 1) (p : ℝ → ℝ) (hp : Continuous p)
    (hn : ∀ z, 0 ≤ p z) (Q : ℝ → ℝ) (hQ : ∀ z, HasDerivAt Q (p z) z)
    {s t : ℝ} (hst : s ≤ t) :
    |Q (H (γ t))-Q (H (γ s))| ≤ ∫ u in s..t, p (H (γ u))*speed γ u := by
  let q := fun u => p (H (γ u))*H (deriv γ u)
  have hdc := (contDiff_infty_iff_deriv.mp hγ).2.continuous
  have ch := H.continuous.comp hγ.continuous
  have hq : Continuous q := (hp.comp ch).mul (H.continuous.comp hdc)
  have hf : (∫ u in s..t, q u) = Q (H (γ t))-Q (H (γ s)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun u => Q (H (γ u))) (fun u _ =>
        (hQ _).comp u (H.hasFDerivAt.comp_hasDerivAt u ((hγ.differentiable (by simp)) u).hasDerivAt))
      (hq.intervalIntegrable _ _)
  rw [← hf]
  refine (intervalIntegral.abs_integral_le_integral_abs hst).trans ?_
  apply intervalIntegral.integral_mono_on hst (hq.abs.intervalIntegrable _ _)
    (((hp.comp ch).mul hdc.norm).intervalIntegrable _ _)
  intro u _
  dsimp only [q]
  rw [abs_mul, abs_of_nonneg (hn _)]
  apply mul_le_mul_of_nonneg_left _ (hn _)
  simpa only [Real.norm_eq_abs, one_mul] using (H.le_opNorm (deriv γ u)).trans
    (mul_le_mul_of_nonneg_right hH (norm_nonneg _))

namespace SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem two_arcs_pay_height_primitive (H : ℂ →L[ℝ] ℝ) (hH : ‖H‖ ≤ 1)
    (p : ℝ → ℝ) (hp : Continuous p) (hn : ∀ z, 0 ≤ p z)
    (Q : ℝ → ℝ) (hQ : ∀ z, HasDerivAt Q (p z) z)
    {t : ℝ} (ht : t ∈ I) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ c.period) :
    2*|Q (H (c.position t v))-Q (H (c.position t u))| ≤ c.cutoffMass H p t := by
  let γ := c.position t
  let G := fun s => Q (H (γ s))
  let w := fun s => p (H (γ s))*speed γ s
  have hs := c.position_slice_smooth ht
  have cg := (speed_smooth hs (c.immersion t ht)).continuous
  have cw : Continuous w := ((hp.comp H.continuous).comp hs.continuous).mul cg
  have bound {a b : ℝ} (hab : a ≤ b) : |G b-G a| ≤ ∫ x in a..b, w x :=
    weightedArcCost γ hs H hH p hp hn Q hQ hab
  have hclosed : G c.period = G 0 := by
    have hz : γ c.period = γ 0 := by simpa using c.periodic t ht 0
    simp only [G,hz]
  have hcomp : |G v-G u| ≤ (∫ x in 0..u, w x) + ∫ x in v..c.period, w x := by
    calc
      _ = |(G 0-G u)+(G v-G c.period)| := by rw [hclosed]; congr 1; ring
      _ ≤ |G 0-G u|+|G v-G c.period| := abs_add_le _ _
      _ = |G u-G 0|+|G c.period-G v| := by rw [abs_sub_comm (G 0),abs_sub_comm (G v)]
      _ ≤ _ := add_le_add (bound hu) (bound hv)
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (cw.intervalIntegrable (μ := volume) 0 u) (cw.intervalIntegrable u v)
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (cw.intervalIntegrable (μ := volume) 0 v) (cw.intervalIntegrable v c.period)
  change 2*|G v-G u| ≤ ∫ x in 0..c.period, w x
  linarith [bound huv]

end SmoothPeriodicImmersion
end MigrationGeometry.Flow
