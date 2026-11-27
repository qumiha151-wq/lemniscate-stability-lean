import Migration.TrueEndpointTransit
import Migration.EndpointMass

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
open ProjectedHeight
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

private theorem weight_gap {δ : ℝ} (dn : 0≤δ) (z : ℝ) :
    0≤weight δ z-weight 0 z ∧ |weight δ z-weight 0 z|≤δ := by
  have zero : weight 0 z=|z| := by simp [weight,Real.sqrt_sq_eq_abs]
  rw [zero]
  have low : |z|≤weight δ z := by
    unfold weight; rw [←Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith only [sq_nonneg δ])
  rw [abs_of_nonneg (sub_nonneg.mpr low)]
  refine ⟨sub_nonneg.mpr low,?_⟩
  have high : weight δ z≤|z|+δ := by
    unfold weight; apply (Real.sqrt_le_iff).mpr
    exact ⟨add_nonneg (abs_nonneg _) dn,by nlinarith only [sq_abs z,mul_nonneg (abs_nonneg z) dn]⟩
  linarith only [high]

theorem moment_zero_error (H : ℂ→L[ℝ] ℝ) (a : ℝ) {t δ : ℝ} (ht : t∈I) (dn : 0≤δ) :
    |c.projectedHeightMoment H a δ t-c.projectedHeightMoment H a 0 t|≤
      δ*c.cutoffMass H (fun z=>|z-a|) t := by
  let x := c.position t
  let h := fun u=>H (x u)-a
  let z := fun u=>H (normal x u)
  let v := speed x
  have ch : Continuous h := (H.continuous.comp (c.position_slice_smooth ht).continuous).sub continuous_const
  have cz : Continuous z := H.continuous.comp (normal_smooth (c.position_slice_smooth ht) (c.immersion t ht)).continuous
  have cv : Continuous v := (speed_smooth (c.position_slice_smooth ht) (c.immersion t ht)).continuous
  have cw (d : ℝ) : Continuous (fun u=>weight d (z u)) := ((cz.pow 2).add continuous_const).sqrt
  change |(∫u in (0:ℝ)..c.period,h u*weight δ (z u)*v u)-(∫u in (0:ℝ)..c.period,h u*weight 0 (z u)*v u)| ≤
    δ*(∫u in (0:ℝ)..c.period,|h u| * v u)
  rw [←intervalIntegral.integral_sub (f:=fun u=>h u*weight δ (z u)*v u) (g:=fun u=>h u*weight 0 (z u)*v u)
    (((ch.mul (cw δ)).mul cv).intervalIntegrable ..) (((ch.mul (cw 0)).mul cv).intervalIntegrable ..),
    ←intervalIntegral.integral_const_mul]
  apply (intervalIntegral.abs_integral_le_integral_abs c.period_pos.le).trans
  apply intervalIntegral.integral_mono_on c.period_pos.le
    ((((ch.mul (cw δ)).mul cv).sub ((ch.mul (cw 0)).mul cv)).abs.intervalIntegrable ..)
    (((ch.abs.mul cv).const_mul δ).intervalIntegrable ..)
  intro u _
  change |h u*weight δ (z u)*v u-h u*weight 0 (z u)*v u|≤δ*(|h u| * v u)
  rw [show h u*weight δ (z u)*v u-h u*weight 0 (z u)*v u=(weight δ (z u)-weight 0 (z u))*(h u*v u) by ring,
    abs_mul,abs_mul,abs_of_nonneg (show 0≤v u from norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right (weight_gap dn _).2 (mul_nonneg (abs_nonneg _) (norm_nonneg _))

theorem force_action_zero_error (flow : c.IsNormalFEF) (e : ℂ) (he : ‖e‖=1)
    {s t δ : ℝ} (a : ℝ) (hd : 0<δ) (st : s≤t) (slab : Icc s t ⊆ I) :
    |(∫v in s..t,c.projectedHeightRate (innerSL ℝ e) a δ v)-
      (c.projectedHeightMoment (innerSL ℝ e) a 0 t-c.projectedHeightMoment (innerSL ℝ e) a 0 s)| ≤
      δ*(c.cutoffMass (innerSL ℝ e) (fun z=>|z-a|) t+c.cutoffMass (innerSL ℝ e) (fun z=>|z-a|) s) := by
  let H := innerSL ℝ e
  let M := c.projectedHeightMoment H a
  rw [c.projectedHeight_two_times flow e he a hd st slab]
  change |(M δ t-M δ s)-(M 0 t-M 0 s)|≤_
  rw [show (M δ t-M δ s)-(M 0 t-M 0 s)=(M δ t-M 0 t)-(M δ s-M 0 s) by ring,mul_add]
  apply (abs_sub _ _).trans
  exact add_le_add (c.moment_zero_error H a (slab (right_mem_Icc.mpr st)) hd.le)
    (c.moment_zero_error H a (slab (left_mem_Icc.mpr st)) hd.le)

theorem force_action_zero_limit (flow : c.IsNormalFEF) (e : ℂ) (he : ‖e‖=1)
    {s t : ℝ} (a : ℝ) (st : s≤t) (slab : Icc s t ⊆ I) :
    Tendsto (fun δ=>∫v in s..t,c.projectedHeightRate (innerSL ℝ e) a δ v) (𝓝[>] (0:ℝ))
      (𝓝 (c.projectedHeightMoment (innerSL ℝ e) a 0 t-c.projectedHeightMoment (innerSL ℝ e) a 0 s)) := by
  let H := innerSL ℝ e
  have err {r : ℝ} (hr : r∈I) : Tendsto (fun δ=>c.projectedHeightMoment H a δ r) (𝓝[>] (0:ℝ))
      (𝓝 (c.projectedHeightMoment H a 0 r)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    let K := c.cutoffMass H (fun z=>|z-a|) r
    have bd : Tendsto (fun δ : ℝ=>δ*K) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa using ((tendsto_id : Tendsto id (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ))).mono_right nhdsWithin_le_nhds).mul_const K
    apply squeeze_zero' (Eventually.of_forall fun _=>dist_nonneg) _ bd
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact c.moment_zero_error H a hr (show 0<δ from hδ).le
  apply ((err (slab (right_mem_Icc.mpr st))).sub (err (slab (left_mem_Icc.mpr st)))).congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (c.projectedHeight_two_times flow e he a (show 0<δ from hδ) st slab).symm

theorem zero_endpoint_cost (flow : c.IsNormalFEF) (e : ℂ) (he : ‖e‖=1)
    {s t a g₀ g₁ : ℝ} (g0 : 0≤g₀) (g1 : 0≤g₁) (st : s≤t) (slab : Icc s t ⊆ I)
    (before : ∀u,inner ℝ e (c.position s u)≤a-g₀) (after : ∀u,a+g₁ ≤ inner ℝ e (c.position t u)) :
    g₁*c.regularizedProjectedLength (innerSL ℝ e) 0 t + g₀*c.regularizedProjectedLength (innerSL ℝ e) 0 s+
      max |c.orientedProjectedArea (innerSL ℝ e) t| (8/(3*(c.bending t)^2))+
      max |c.orientedProjectedArea (innerSL ℝ e) s| (8/(3*(c.bending s)^2)) ≤
      c.projectedHeightMoment (innerSL ℝ e) a 0 t-c.projectedHeightMoment (innerSL ℝ e) a 0 s := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (c.force_action_zero_limit flow e he a st slab)
  filter_upwards [self_mem_nhdsWithin] with δ hd
  have dp : 0<δ := hd
  let H := innerSL ℝ e
  have monotone (r : ℝ) (hr : r∈I) : c.regularizedProjectedLength H 0 r≤c.regularizedProjectedLength H δ r := by
    let z := fun u=>H (normal (c.position r) u)
    have cz : Continuous z := H.continuous.comp (normal_smooth (c.position_slice_smooth hr) (c.immersion r hr)).continuous
    have cv := (speed_smooth (c.position_slice_smooth hr) (c.immersion r hr)).continuous
    have cw (d : ℝ) : Continuous (fun u=>weight d (z u)) := ((cz.pow 2).add continuous_const).sqrt
    apply intervalIntegral.integral_mono_on c.period_pos.le (((cw 0).mul cv).intervalIntegrable ..) (((cw δ).mul cv).intervalIntegrable ..)
    intro u _; exact mul_le_mul_of_nonneg_right (sub_nonneg.mp (weight_gap dp.le _).1) (norm_nonneg _)
  apply le_trans _ (c.projectedHeight_uniform_endpoint_cost flow e he dp st slab before after)
  apply add_le_add_left; apply add_le_add_left
  exact add_le_add (mul_le_mul_of_nonneg_left (monotone t (slab (right_mem_Icc.mpr st))) g1)
    (mul_le_mul_of_nonneg_left (monotone s (slab (left_mem_Icc.mpr st))) g0)

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.force_action_zero_limit
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.zero_endpoint_cost
