import Migration.ProjectedHeightTransit

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
open ProjectedHeight
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

/-- Oriented horizontal projection of the material parameter derivative, when H is vertical. -/
def signedProjectedSpeed (H : ℂ →L[ℝ] ℝ) (t u : ℝ) :=
  H (normal (c.position t) u) * speed (c.position t) u

/-- Oriented projected area, with the convention A = ∮ h dx. -/
def orientedProjectedArea (H : ℂ →L[ℝ] ℝ) (t : ℝ) :=
  ∫ u in 0..c.period, H (c.position t u) * c.signedProjectedSpeed H t u

private theorem signedSpeed_cont (H : ℂ →L[ℝ] ℝ) {t : ℝ} (ht : t ∈ I) :
    Continuous (c.signedProjectedSpeed H t) :=
  (H.continuous.comp (normal_smooth (c.position_slice_smooth ht) (c.immersion t ht)).continuous).mul
    (speed_smooth (c.position_slice_smooth ht) (c.immersion t ht)).continuous

theorem signedProjectedSpeed_period (H : ℂ →L[ℝ] ℝ) {t : ℝ} (ht : t ∈ I) :
    (∫ u in 0..c.period, c.signedProjectedSpeed H t u) = 0 := by
  let x := c.position t
  have hd u : HasDerivAt (fun s => H (Complex.I * x s)) (c.signedProjectedSpeed H t u) u := by
    have hx := (position_hasDerivAt (c.position_slice_smooth ht) (c.immersion t ht) u).const_mul Complex.I
    have dh := H.hasFDerivAt.comp_hasDerivAt u hx
    change HasDerivAt (fun s => H (Complex.I*x s))
      (H (Complex.I*(speed x u • tangent x u))) u at dh
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm] at dh
    exact dh
  have ft := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=c.period)
    (fun u _ => hd u) ((c.signedSpeed_cont H ht).intervalIntegrable ..)
  have ends := c.periodic t ht 0
  simp only [zero_add] at ends
  simpa [x,ends] using ft

/-- Every constant height offset contributes exactly zero to the signed projection. -/
theorem orientedProjectedArea_sub_height (H : ℂ →L[ℝ] ℝ) {t : ℝ} (ht : t ∈ I) (a : ℝ) :
    (∫ u in 0..c.period, (H (c.position t u)-a)*c.signedProjectedSpeed H t u) =
      c.orientedProjectedArea H t := by
  have ch := H.continuous.comp (c.position_slice_smooth ht).continuous
  have cz := c.signedSpeed_cont H ht
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub (f:=fun u => H (c.position t u)*c.signedProjectedSpeed H t u)
    (g:=fun u => a*c.signedProjectedSpeed H t u) ((ch.mul cz).intervalIntegrable ..) ((cz.const_mul a).intervalIntegrable ..),
    intervalIntegral.integral_const_mul, c.signedProjectedSpeed_period H ht, mul_zero, sub_zero]
  rfl

/-- The area is dominated by the regularized absolute first moment about every reference height. -/
theorem abs_orientedProjectedArea_le (H : ℂ →L[ℝ] ℝ) {δ t : ℝ} (hd : 0<δ) (ht : t ∈ I) (a : ℝ) :
    |c.orientedProjectedArea H t| ≤ ∫ u in 0..c.period,
      |H (c.position t u)-a| * weight δ (H (normal (c.position t) u)) * speed (c.position t) u := by
  let x := c.position t
  have hs := c.position_slice_smooth ht
  have hr := c.immersion t ht
  have ch := (H.continuous.comp hs.continuous).sub (continuous_const (y:=a))
  have cn := H.continuous.comp (normal_smooth hs hr).continuous
  have cv := (speed_smooth hs hr).continuous
  have cw := continuous_iff_continuousAt.mpr fun z => (weight_derivative hd z).continuousAt
  rw [← c.orientedProjectedArea_sub_height H ht a]
  apply (intervalIntegral.abs_integral_le_integral_abs c.period_pos.le).trans
  apply intervalIntegral.integral_mono_on c.period_pos.le
    (((ch.mul (c.signedSpeed_cont H ht)).abs).intervalIntegrable ..)
    (((ch.abs.mul (cw.comp cn)).mul cv).intervalIntegrable ..)
  intro u _
  have hz : |H (normal x u)| ≤ weight δ (H (normal x u)) := by
    dsimp [weight]
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    linarith only [sq_nonneg δ]
  change |(H (x u)-a)*(H (normal x u)*speed x u)| ≤
    |H (x u)-a| * weight δ (H (normal x u))*speed x u
  have speedNonneg : 0 ≤ speed x u := norm_nonneg _
  rw [abs_mul,abs_mul,abs_of_nonneg speedNonneg,← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz (abs_nonneg _)) speedNonneg

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

theorem projectedHeight_area_separation (flow : c.IsNormalFEF) (e : ℂ) (he : ‖e‖=1)
    {level g₀ g₁ δ s t : ℝ} (hd : 0<δ) (order : s≤t) (slab : Icc s t⊆I)
    (before : ∀ u, inner ℝ e (c.position s u)≤level-g₀)
    (after : ∀ u, level+g₁ ≤ inner ℝ e (c.position t u)) :
    g₁*c.regularizedProjectedLength (innerSL ℝ e) δ t+
      g₀*c.regularizedProjectedLength (innerSL ℝ e) δ s+
      |c.orientedProjectedArea (innerSL ℝ e) t|+|c.orientedProjectedArea (innerSL ℝ e) s| ≤
      ∫ v in s..t, c.projectedHeightRate (innerSL ℝ e) level δ v := by
  let H := innerSL ℝ e
  have ht := slab (right_mem_Icc.mpr order)
  have hs := slab (left_mem_Icc.mpr order)
  have top := c.abs_orientedProjectedArea_le H hd ht (level+g₁)
  have bot := c.abs_orientedProjectedArea_le H hd hs (level+(-g₀))
  have hi (u : ℝ) : 0 ≤ H (c.position t u)-(level+g₁) := sub_nonneg.mpr (after u)
  have lo (u : ℝ) : H (c.position s u)-(level+(-g₀)) ≤ 0 := by
    change inner ℝ e (c.position s u)-(level+(-g₀)) ≤ 0
    linarith only [before u]
  simp_rw [abs_of_nonneg (hi _)] at top
  simp_rw [abs_of_nonpos (lo _),neg_mul] at bot
  rw [intervalIntegral.integral_neg] at bot
  change |c.orientedProjectedArea H t| ≤ c.projectedHeightMoment H (level+g₁) δ t at top
  change |c.orientedProjectedArea H s| ≤ -c.projectedHeightMoment H (level+(-g₀)) δ s at bot
  rw [← c.moment_offset H hd ht level g₁] at top
  rw [← c.moment_offset H hd hs level (-g₀)] at bot
  rw [c.projectedHeight_two_times flow e he level hd order slab]
  change _ ≤ c.projectedHeightMoment H level δ t - c.projectedHeightMoment H level δ s
  change g₁*c.regularizedProjectedLength H δ t+g₀*c.regularizedProjectedLength H δ s+
    |c.orientedProjectedArea H t|+|c.orientedProjectedArea H s| ≤ _
  linarith only [top,bot]

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.projectedHeight_area_separation
