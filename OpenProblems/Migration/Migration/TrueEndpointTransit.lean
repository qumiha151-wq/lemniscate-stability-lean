import Migration.TrueEndpointMoment

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
open ProjectedHeight
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

private theorem actual_residual {t : ℝ} (ht : t∈I) (e : ℂ) (he : ‖e‖=1) (a : ℝ) {δ : ℝ} (hd : 0<δ)
    (side : (∀u,a≤ inner ℝ e (c.position t u)) ∨ (∀u,inner ℝ e (c.position t u)≤a)) :
    8/(3*(c.bending t)^2) ≤ ∫u in (0:ℝ)..c.period,
      |(innerSL ℝ e) (c.position t u)-a| * weight δ ((innerSL ℝ e) (normal (c.position t) u)) * speed (c.position t) u := by
  let H := innerSL ℝ e
  let γ := c.position t
  have low : 8/(3*(c.bending t)^2) ≤ ∫u in (0:ℝ)..c.period,|H (γ u)-a| * |H (normal γ u)| * speed γ u := by
    rcases side with up|down
    · have hi (u) : 0≤H (γ u)-a := sub_nonneg.mpr (up u)
      simp_rw [abs_of_nonneg (hi _)]
      exact c.true_far_moment ht e he a up
    · have side' (u) : -a≤ inner ℝ (-e) (c.position t u) := by rw [inner_neg_left]; exact neg_le_neg (down u)
      have low := c.true_far_moment ht (-e) (by simpa using he) (-a) side'
      simp only [inner_neg_left,abs_neg,sub_neg_eq_add] at low
      have neg (u) : |H (γ u)-a|= -(H (γ u))+a := by
        have hn : H (γ u)-a≤0 := sub_nonpos.mpr (down u)
        rw [abs_of_nonpos hn]; ring
      simp_rw [neg]; exact low
  have ch := H.continuous.comp (c.position_slice_smooth ht).continuous
  have cn := H.continuous.comp (normal_smooth (c.position_slice_smooth ht) (c.immersion t ht)).continuous
  have cw := (continuous_iff_continuousAt.mpr fun z=>(weight_derivative hd z).continuousAt).comp cn
  have cv := (speed_smooth (c.position_slice_smooth ht) (c.immersion t ht)).continuous
  apply low.trans
  apply intervalIntegral.integral_mono_on c.period_pos.le
    ((((ch.sub continuous_const).abs.mul cn.abs).mul cv).intervalIntegrable ..)
    ((((ch.sub continuous_const).abs.mul cw).mul cv).intervalIntegrable ..)
  intro u _
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  change |H (normal γ u)| ≤ Real.sqrt ((H (normal γ u))^2+δ^2)
  rw [←Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by linarith only [sq_nonneg δ])

private theorem moment_offset (H : ℂ →L[ℝ] ℝ) {δ t : ℝ} (hd : 0<δ) (ht : t ∈ I) (l a : ℝ) :
    c.projectedHeightMoment H l δ t - a*c.regularizedProjectedLength H δ t =
    c.projectedHeightMoment H (l+a) δ t := by
  let h := fun u => H (c.position t u)
  let w := fun u => weight δ (H (normal (c.position t) u))
  let v := speed (c.position t)
  have ch := H.continuous.comp (c.position_slice_smooth ht).continuous
  have cn := H.continuous.comp (normal_smooth (c.position_slice_smooth ht) (c.immersion t ht)).continuous
  have cw := (continuous_iff_continuousAt.mpr fun z => (weight_derivative hd z).continuousAt).comp cn
  have cv := (speed_smooth (c.position_slice_smooth ht) (c.immersion t ht)).continuous
  unfold projectedHeightMoment regularizedProjectedLength
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_sub
    (f:=fun u => (h u-l)*w u*v u) (g:=fun u => a*(w u*v u))
    ((((ch.sub (continuous_const (y:=l))).mul cw).mul cv).intervalIntegrable ..)
    (((cw.mul cv).const_mul a).intervalIntegrable ..)]
  apply intervalIntegral.integral_congr
  intro u _
  ring

theorem projectedHeight_uniform_endpoint_cost (flow : c.IsNormalFEF) (e : ℂ) (he : ‖e‖=1)
    {level g₀ g₁ δ s t : ℝ} (hd : 0<δ) (order : s≤t) (slab : Icc s t⊆I)
    (before : ∀ u, inner ℝ e (c.position s u)≤level-g₀)
    (after : ∀ u, level+g₁ ≤ inner ℝ e (c.position t u)) :
    g₁*c.regularizedProjectedLength (innerSL ℝ e) δ t+
      g₀*c.regularizedProjectedLength (innerSL ℝ e) δ s+
      max |c.orientedProjectedArea (innerSL ℝ e) t| (8/(3*(c.bending t)^2))+
      max |c.orientedProjectedArea (innerSL ℝ e) s| (8/(3*(c.bending s)^2)) ≤
      ∫ v in s..t, c.projectedHeightRate (innerSL ℝ e) level δ v := by
  let H := innerSL ℝ e
  have ht := slab (right_mem_Icc.mpr order)
  have hs := slab (left_mem_Icc.mpr order)
  have At := c.abs_orientedProjectedArea_le H hd ht (level+g₁)
  have As := c.abs_orientedProjectedArea_le H hd hs (level+(-g₀))
  have hi (u : ℝ) : 0 ≤ H (c.position t u)-(level+g₁) := sub_nonneg.mpr (after u)
  have lo (u : ℝ) : H (c.position s u)-(level+(-g₀)) ≤ 0 := by
    change inner ℝ e (c.position s u)-(level+(-g₀)) ≤ 0
    linarith only [before u]
  have wt := c.actual_residual ht e he (level+g₁) hd (Or.inl after)
  have ws := c.actual_residual hs e he (level+(-g₀)) hd (Or.inr (fun u=>by linarith only [before u]))
  have top := max_le At wt
  have bot := max_le As ws
  simp_rw [abs_of_nonneg (hi _)] at top
  simp_rw [abs_of_nonpos (lo _),neg_mul] at bot
  rw [intervalIntegral.integral_neg] at bot
  change _ ≤ c.projectedHeightMoment H (level+g₁) δ t at top
  change _ ≤ -c.projectedHeightMoment H (level+(-g₀)) δ s at bot
  rw [← c.moment_offset H hd ht level g₁] at top
  rw [← c.moment_offset H hd hs level (-g₀)] at bot
  rw [c.projectedHeight_two_times flow e he level hd order slab]
  change _ ≤ c.projectedHeightMoment H level δ t - c.projectedHeightMoment H level δ s
  change g₁*c.regularizedProjectedLength H δ t+g₀*c.regularizedProjectedLength H δ s+
    max |c.orientedProjectedArea H t| (8/(3*(c.bending t)^2))+
    max |c.orientedProjectedArea H s| (8/(3*(c.bending s)^2)) ≤ _
  linarith only [top,bot]

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.projectedHeight_uniform_endpoint_cost
