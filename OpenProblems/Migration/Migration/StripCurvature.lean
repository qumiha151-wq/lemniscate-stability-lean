import Migration.TangentExcursion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! One monotone-height excursion requires enough squared curvature to
control the inverse width of a closed immersed curve. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow

private theorem excursion_variation {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ)
    (hr : ∀ u, deriv γ u ≠ 0) {a p b : ℝ} (hap : a≤p) (hpb : p≤b)
    (hpx : (tangent γ p).re=0) (hay : (tangent γ a).im=0) (hby : (tangent γ b).im=0) :
    2 ≤ ∫ u in a..b, |curvature γ u| * |(tangent γ u).im| * speed γ u := by
  let q := fun u => -(speed γ u*curvature γ u)*(tangent γ u).im
  have hq : Continuous q := (((speed_smooth hγ hr).continuous.mul
    (curvature_smooth hγ hr).continuous).neg).mul (Complex.continuous_im.comp (tangent_smooth hγ hr).continuous)
  have hd (u : ℝ) : HasDerivAt (fun x => (tangent γ x).re) (q u) u := by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u (tangent_hasDerivAt hγ hr u)
    apply h.congr_deriv
    simp [q,normal,Complex.mul_re,Complex.mul_im]
  have hnorm (u : ℝ) (hu : (tangent γ u).im=0) : |(tangent γ u).re|=1 := by
    have h := tangent_components_sq hr u
    rw [hu] at h
    nlinarith [sq_abs (tangent γ u).re,abs_nonneg (tangent γ u).re]
  have hpiece (r s : ℝ) (hrs : r≤s) :
      |(tangent γ s).re-(tangent γ r).re| ≤ ∫ u in r..s, |q u| := by
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) (hq.intervalIntegrable r s)]
    exact intervalIntegral.abs_integral_le_integral_abs hrs
  have hleft := hpiece a p hap
  have hright := hpiece p b hpb
  rw [hpx,zero_sub,abs_neg,hnorm a hay] at hleft
  rw [hpx,sub_zero,hnorm b hby] at hright
  calc
    (2:ℝ) ≤ (∫ u in a..p, |q u|)+(∫ u in p..b, |q u|) := by linarith
    _ = _ := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hq.abs.intervalIntegrable a p)
        (hq.abs.intervalIntegrable p b)]
      apply intervalIntegral.integral_congr
      intro u _
      simp [q,abs_mul,abs_of_pos (speed_pos hr u)]
      ring

namespace SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

/-- Every smooth closed regular plane curve satisfies E W ≥ 2, where W
is its actual vertical span. The assertion is independent of the time PDE. -/
theorem bending_mul_verticalWidth {t : ℝ} (ht : t ∈ I) : 2 ≤ c.bending t*c.verticalWidth t := by
  let γ := c.position t
  let k := curvature γ
  let g := speed γ
  let Y := fun u => (tangent γ u).im
  have hs : ContDiff ℝ ∞ γ := c.position_slice_smooth ht
  have hr := c.immersion t ht
  have hp := c.periodic t ht
  obtain ⟨j,a,p,b,σ,hja,hap,hpb,hbj,hσ,hpx,hay,hby,hsgn⟩ :=
    tangent_excursion c.period_pos hs hr hp
  have hab := hap.trans hpb
  have hY : Continuous Y := Complex.continuous_im.comp (tangent_smooth hs hr).continuous
  have hk : Continuous k := (curvature_smooth hs hr).continuous
  have hg : Continuous g := (speed_smooth hs hr).continuous
  have hg0 (u) : 0≤g u := (speed_pos hr u).le
  have hY1 (u) : |Y u|≤1 := (Complex.abs_im_le_norm _).trans_eq (tangent_unit hr u)
  have hsign (u) (hu : u ∈ Icc a b) : |Y u|=σ*Y u := by
    have h : 0≤σ*Y u := hsgn u hu
    rcases hσ with hσ | hσ
    · rw [hσ,one_mul] at h ⊢
      exact abs_of_nonneg h
    · rw [hσ,neg_one_mul] at h ⊢
      exact abs_of_nonpos (neg_nonneg.mp h)
  have hcs := interval_integral_mul_sq_le (hk.abs.mul hg.sqrt) (hY.abs.mul hg.sqrt) hab
  have hA : (∫ u in a..b, (|k u| * Real.sqrt (g u))^2) = ∫ u in a..b, k u^2*g u := by
    apply intervalIntegral.integral_congr
    intro u _
    simp only [mul_pow,sq_abs,Real.sq_sqrt (hg0 u)]
  have hB : (∫ u in a..b, (|Y u| * Real.sqrt (g u))^2) = ∫ u in a..b, Y u^2*g u := by
    apply intervalIntegral.integral_congr
    intro u _
    simp only [mul_pow,sq_abs,Real.sq_sqrt (hg0 u)]
  have hC : (∫ u in a..b, (|k u| * Real.sqrt (g u))*(|Y u| * Real.sqrt (g u))) =
      ∫ u in a..b, |k u| * |Y u| * g u := by
    apply intervalIntegral.integral_congr
    intro u _
    calc _ = |k u| * |Y u| * (Real.sqrt (g u))^2 := by ring
         _ = _ := by rw [Real.sq_sqrt (hg0 u)]
  change (∫ u in a..b, (|k u| * Real.sqrt (g u))*(|Y u| * Real.sqrt (g u)))^2 ≤
    (∫ u in a..b, (|k u| * Real.sqrt (g u))^2)*(∫ u in a..b, (|Y u| * Real.sqrt (g u))^2) at hcs
  rw [hA,hB,hC] at hcs
  have hv : 2 ≤ ∫ u in a..b, |k u| * |Y u| * g u :=
    excursion_variation hs hr hap hpb hpx hay hby
  have hKp : Function.Periodic (fun u => k u^2*g u) c.period := by
    intro u
    dsimp only [k,g]
    rw [curvature_periodic hs hr hp u,speed_periodic hs hp u]
  have hK : (∫ u in a..b, k u^2*g u) ≤ 2*c.bending t := by
    have h := intervalIntegral.integral_mono_interval (μ := volume) hja hab hbj
      (f := fun u => k u^2*g u) (Eventually.of_forall (fun u => mul_nonneg (sq_nonneg _) (hg0 u)))
      (((hk.pow 2).mul hg).intervalIntegrable _ _)
    rw [hKp.intervalIntegral_add_eq j 0,zero_add] at h
    unfold bending
    linarith
  have hheight (u : ℝ) : (γ u).im ∈ Icc (c.bottom t) (c.top t) := by
    obtain ⟨y,hy,hey⟩ := hp.exists_mem_Ico₀ c.period_pos u
    change (c.position t u).im ∈ _
    rw [hey]
    exact (c.height_range_of_slice_continuous hs.continuous).1 y ⟨hy.1,hy.2.le⟩
  have hYint : (∫ u in a..b, Y u^2*g u) ≤ c.verticalWidth t := by
    have hder (u : ℝ) : HasDerivAt (fun x => σ*(γ x).im) (σ*Y u*g u) u := by
      have hh := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt u (position_hasDerivAt hs hr u)).const_mul σ
      apply hh.congr_deriv
      simp [Y,g]
      ring
    calc
      _ ≤ ∫ u in a..b, σ*Y u*g u := by
        apply intervalIntegral.integral_mono_on hab (((hY.pow 2).mul hg).intervalIntegrable _ _)
          (((hY.const_mul σ).mul hg).intervalIntegrable _ _)
        intro u hu
        apply mul_le_mul_of_nonneg_right _ (hg0 u)
        change Y u^2≤σ*Y u
        rw [← hsign u hu,← sq_abs (Y u)]
        nlinarith [mul_nonneg (abs_nonneg (Y u)) (sub_nonneg.mpr (hY1 u))]
      _ = σ*(γ b).im-σ*(γ a).im := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u _ => hder u) (((hY.const_mul σ).mul hg).intervalIntegrable _ _)
      _ ≤ _ := by
        rcases hσ with h | h <;> rw [h] <;> unfold verticalWidth <;>
          linarith [(hheight a).1,(hheight a).2,(hheight b).1,(hheight b).2]
  have hnon : 0 ≤ ∫ u in a..b, Y u^2*g u :=
    intervalIntegral.integral_nonneg_of_forall hab (fun u => mul_nonneg (sq_nonneg _) (hg0 u))
  have hcompare := mul_le_mul hK hYint hnon (mul_nonneg (by norm_num) (c.bending_nonneg t))
  have hfour := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hv 2
  nlinarith [hfour.trans (hcs.trans hcompare)]

end SmoothPeriodicImmersion
end MigrationGeometry.Flow
