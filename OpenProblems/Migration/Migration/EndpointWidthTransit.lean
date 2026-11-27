import Migration.AngularEndpointMoment
import Migration.OrientedAreaTransit

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
open ProjectedHeight
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

private theorem absolute_variation {g v : ℝ→ℝ} (dg : ∀u,HasDerivAt g (v u) u)
    (cv : Continuous v) {L u b : ℝ} (endg : g L=g 0)
    (hu : 0≤u) (hub : u≤b) (hb : b≤L) : 2*|g b-g u|≤∫s in (0:ℝ)..L,|v s| := by
  have arc (l r : ℝ) (lr : l≤r) : |g r-g l|≤∫s in l..r,|v s| := by
    rw [←intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _=>dg s) (cv.intervalIntegrable ..)]
    exact intervalIntegral.abs_integral_le_integral_abs lr
  have h := arc b L hb
  rw [endg] at h
  have tri := abs_sub_le (g b) (g 0) (g u)
  rw [abs_sub_comm (g b) (g 0),abs_sub_comm (g 0) (g u)] at tri
  have j := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (cv.abs.intervalIntegrable 0 u) (cv.abs.intervalIntegrable u b)
  have k := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (cv.abs.intervalIntegrable 0 b) (cv.abs.intervalIntegrable b L)
  linarith only [arc 0 u hu,arc u b hub,h,tri,j,k]

def endpointHeightDifference (H : ℂ→L[ℝ] ℝ) (t u v : ℝ) :=
  H (c.position t v)-H (c.position t u)

/-- An arbitrary ordered pair of material labels gives a lower bound at a
single endpoint. Taking both extrema realizes the squared directional width. -/
theorem square_height_moment (H : ℂ→L[ℝ] ℝ) (hH : ‖H‖≤1)
    {t a δ u v : ℝ} (ht : t∈I) (hd : 0<δ) (hu : 0≤u) (hov : u≤v) (hv : v≤c.period)
    (side : 0≤(H (c.position t v)-a)*(H (c.position t u)-a)) :
    δ*(c.endpointHeightDifference H t u v)^2 ≤ ∫s in (0:ℝ)..c.period,
      |H (c.position t s)-a| * weight δ (H (normal (c.position t) s)) * speed (c.position t) s := by
  let x := c.position t
  let y := fun s => H (x s)-a
  let g := fun s => (y s)^2/2
  let q := fun s=>y s*H (deriv x s)
  have sm := c.position_slice_smooth ht
  have cD := (contDiff_infty_iff_deriv.mp sm).2.continuous
  have cy : Continuous y := (H.continuous.comp sm.continuous).sub continuous_const
  have cq : Continuous q := cy.mul (H.continuous.comp cD)
  have gd (s : ℝ) : HasDerivAt g (q s) s := by
    have d := (H.hasFDerivAt.comp_hasDerivAt s ((sm.differentiable (by simp)) s).hasDerivAt).sub_const a
    apply ((d.pow 2).div_const 2).congr_deriv
    dsimp [q,y,x]; ring
  have per := c.periodic t ht 0
  rw [zero_add] at per
  have ends : g c.period = g 0 := by dsimp [g,y,x]; rw [per]
  have vari := absolute_variation gd cq ends hu hov hv
  have av : |y v-y u|≤|y v+y u| := by
    apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
    simp only [sq_abs]; change 0≤y v*y u at side; nlinarith only [side]
  have pw := mul_le_mul_of_nonneg_left av (abs_nonneg (y v-y u))
  rw [←sq, sq_abs,←abs_mul,show (y v-y u)*(y v+y u)=2*(g v-g u) by dsimp [g]; ring,
    abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at pw
  have diff : c.endpointHeightDifference H t u v = y v-y u := by dsimp [endpointHeightDifference,y,x]; ring
  rw [diff]
  have cc := H.continuous.comp (normal_smooth sm (c.immersion t ht)).continuous
  have cw := (continuous_iff_continuousAt.mpr fun z=>(weight_derivative hd z).continuousAt).comp cc
  have ca := (speed_smooth sm (c.immersion t ht)).continuous
  apply (mul_le_mul_of_nonneg_left (pw.trans vari) hd.le).trans
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on c.period_pos.le ((cq.abs.const_mul _).intervalIntegrable ..)
    (((cy.abs.mul cw).mul ca).intervalIntegrable ..)
  intro s _
  have bound := (H.le_opNorm (deriv x s)).trans (mul_le_mul_of_nonneg_right hH (norm_nonneg _))
  simp only [Real.norm_eq_abs,one_mul] at bound
  have dw : δ≤weight δ (H (normal (x) s)) := by
    unfold weight
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    linarith only [sq_nonneg (H (normal x s))]
  change δ*|y s*H (deriv x s)|≤|y s| * weight δ (H (normal x s))*‖deriv x s‖
  rw [abs_mul]
  calc
    _ = |y s| * (δ*|H (deriv x s)|) := by ring
    _ ≤ |y s| * (weight δ (H (normal x s))*‖deriv x s‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul dw bound (abs_nonneg _) (Real.sqrt_nonneg _)) (abs_nonneg _)
    _ = _ := by ring

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

theorem projectedHeight_width_area_separation (flow : c.IsNormalFEF) (e : ℂ) (he : ‖e‖=1)
    {level g₀ g₁ δ s t : ℝ} (hd : 0<δ) (order : s≤t) (slab : Icc s t⊆I)
    {u₀ v₀ u₁ v₁ : ℝ} (hu₀ : 0≤u₀) (ho₀ : u₀≤v₀) (hv₀ : v₀≤c.period)
    (hu₁ : 0≤u₁) (ho₁ : u₁≤v₁) (hv₁ : v₁≤c.period)
    (before : ∀ u, inner ℝ e (c.position s u)≤level-g₀)
    (after : ∀ u, level+g₁ ≤ inner ℝ e (c.position t u)) :
    g₁*c.regularizedProjectedLength (innerSL ℝ e) δ t+
      g₀*c.regularizedProjectedLength (innerSL ℝ e) δ s+
      max |c.orientedProjectedArea (innerSL ℝ e) t| (δ*(c.endpointHeightDifference (innerSL ℝ e) t u₁ v₁)^2)+
      max |c.orientedProjectedArea (innerSL ℝ e) s| (δ*(c.endpointHeightDifference (innerSL ℝ e) s u₀ v₀)^2) ≤
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
  have op : ‖H‖≤1 := by dsimp [H]; rw [innerSL_apply_norm,he]
  have wt := c.square_height_moment H op ht hd hu₁ ho₁ hv₁ (mul_nonneg (hi _) (hi _))
  have ws := c.square_height_moment H op hs hd hu₀ ho₀ hv₀ (mul_nonneg_of_nonpos_of_nonpos (lo _) (lo _))
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
    max |c.orientedProjectedArea H t| (δ*(c.endpointHeightDifference H t u₁ v₁)^2)+
    max |c.orientedProjectedArea H s| (δ*(c.endpointHeightDifference H s u₀ v₀)^2) ≤ _
  linarith only [top,bot]

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.projectedHeight_width_area_separation
