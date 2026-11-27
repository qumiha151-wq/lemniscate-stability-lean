import Migration.ProjectedHeightEvolution

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
open ProjectedHeight
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem unit_projection_identity {e : ℂ} (he : ‖e‖=1) (v : ℂ) :
    ((innerSL ℝ e) v)^2+((innerSL ℝ e) (Complex.I*v))^2=‖v‖^2 := by
  change (inner ℝ e v)^2+(inner ℝ e (Complex.I*v))^2=_
  calc
    _ = ‖e‖^2*‖v‖^2 := by
      rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq,Complex.inner,Complex.inner]
      simp only [Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.conj_re,
        Complex.conj_im,Complex.I_re,Complex.I_im]
      ring
    _ = _ := by rw [he,one_pow,one_mul]

private theorem rate_cont (H : ℂ →L[ℝ] ℝ) (level : ℝ) {δ : ℝ} (hd : 0<δ) :
    ContinuousOn (c.projectedHeightRate H level δ) I := by
  have hh := (H.continuous.comp_continuousOn c.joint_smooth.continuousOn).sub
    (continuousOn_const (c:=level))
  have hn := H.continuous.comp_continuousOn c.normal_joint_smooth.continuousOn
  have hw := continuous_iff_continuousAt.mpr fun z => (weight_derivative hd z).continuousAt
  have positive (z : ℝ) : 0<weight δ z := Real.sqrt_pos.mpr (by positivity)
  have ca : Continuous (bulk δ) :=
    (continuous_id.mul continuous_const).div hw (fun z => (positive z).ne')
  have cb : Continuous (tip δ) :=
    continuous_const.div (hw.pow 3) (fun z => pow_ne_zero _ (positive z).ne')
  apply continuousOn_intervalIntegral_of_isOpen (a:=0) (b:=c.period)
    (F:=fun t u => force (c.position t) u*(-bulk δ (H (normal (c.position t) u))+
      (H (c.position t u)-level)*curvature (c.position t) u*tip δ (H (normal (c.position t) u)))*
      speed (c.position t) u) c.time_open
  exact ((c.force_joint_smooth.continuousOn.mul ((ca.comp_continuousOn hn).neg.add
    ((hh.mul c.curvature_joint_smooth.continuousOn).mul (cb.comp_continuousOn hn)))).mul
    c.speed_joint_smooth.continuousOn).mono (fun _ h => ⟨h.1,mem_univ _⟩)

def regularizedProjectedLength (H : ℂ →L[ℝ] ℝ) (δ t : ℝ) :=
  ∫ u in 0..c.period, weight δ (H (normal (c.position t) u))*speed (c.position t) u

/-- Every genuine closed flow gives the two-time identity in every unit
    direction, including directions with degenerate tangencies. -/
theorem projectedHeight_two_times (flow : c.IsNormalFEF) (e : ℂ) (he : ‖e‖=1)
    (level : ℝ) {δ s t : ℝ} (hd : 0<δ) (order : s≤t) (slab : Icc s t⊆I) :
    (∫ v in s..t, c.projectedHeightRate (innerSL ℝ e) level δ v)=
      c.projectedHeightMoment (innerSL ℝ e) level δ t-c.projectedHeightMoment (innerSL ℝ e) level δ s := by
  let H := innerSL ℝ e
  have der v hv := c.projectedHeight_evolution flow H (unit_projection_identity he) level hd (slab (a:=v) hv)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le order
    (fun v hv => (der v hv).continuousAt.continuousWithinAt)
    (fun v hv => der v ⟨hv.1.le,hv.2.le⟩) (((c.rate_cont H level hd).mono slab).intervalIntegrable_of_Icc order)

private theorem moment_bounds (H : ℂ →L[ℝ] ℝ) (level d : ℝ) {δ t : ℝ} (hd : 0<δ) (ht : t∈I) :
    ((∀ u, H (c.position t u)-level≤d) →
      c.projectedHeightMoment H level δ t≤d*c.regularizedProjectedLength H δ t) ∧
    ((∀ u, d≤H (c.position t u)-level) →
      d*c.regularizedProjectedLength H δ t≤c.projectedHeightMoment H level δ t) := by
  let x := c.position t
  let h := fun u => H (x u)-level
  let v := fun u => weight δ (H (normal x u))*speed x u
  have hs := c.position_slice_smooth ht
  have hr := c.immersion t ht
  have ch : Continuous h := (H.continuous.comp hs.continuous).sub continuous_const
  have cw := continuous_iff_continuousAt.mpr fun z => (weight_derivative hd z).continuousAt
  have cv : Continuous v := ((cw.comp H.continuous).comp (normal_smooth hs hr).continuous).mul
    (speed_smooth hs hr).continuous
  have pos (u : ℝ) : 0≤v u := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have rewriteH : c.projectedHeightMoment H level δ t = ∫ u in 0..c.period, h u*v u := by
    apply intervalIntegral.integral_congr
    intro u _
    change h u*weight δ (H (normal x u))*speed x u=h u*(weight δ (H (normal x u))*speed x u)
    ring
  rw [rewriteH,regularizedProjectedLength,← intervalIntegral.integral_const_mul]
  constructor <;> intro bound
  · exact intervalIntegral.integral_mono_on c.period_pos.le ((ch.mul cv).intervalIntegrable ..)
      ((cv.const_mul d).intervalIntegrable ..) (fun u _ => mul_le_mul_of_nonneg_right (bound u) (pos u))
  · exact intervalIntegral.integral_mono_on c.period_pos.le ((cv.const_mul d).intervalIntegrable ..)
      ((ch.mul cv).intervalIntegrable ..) (fun u _ => mul_le_mul_of_nonneg_right (bound u) (pos u))

/-- Separation of the complete endpoint images forces a lower bound
    on the time integral of the two actual force contributions. -/
theorem projectedHeight_separation (flow : c.IsNormalFEF) (e : ℂ) (he : ‖e‖=1)
    {level g₀ g₁ δ s t : ℝ} (hd : 0<δ) (order : s≤t) (slab : Icc s t⊆I)
    (before : ∀ u, inner ℝ e (c.position s u)≤level-g₀)
    (after : ∀ u, level+g₁ ≤ inner ℝ e (c.position t u)) :
    g₁*c.regularizedProjectedLength (innerSL ℝ e) δ t+
      g₀*c.regularizedProjectedLength (innerSL ℝ e) δ s ≤
      ∫ v in s..t, c.projectedHeightRate (innerSL ℝ e) level δ v := by
  let H := innerSL ℝ e
  have start := (c.moment_bounds H level (-g₀) hd (slab (left_mem_Icc.mpr order))).1
    (fun u => by change inner ℝ e (c.position s u)-level ≤ -g₀; linarith only [before u])
  have finish := (c.moment_bounds H level g₁ hd (slab (right_mem_Icc.mpr order))).2
    (fun u => by change g₁ ≤ inner ℝ e (c.position t u)-level; linarith only [after u])
  rw [c.projectedHeight_two_times flow e he level hd order slab]
  change _ ≤ c.projectedHeightMoment H level δ t-c.projectedHeightMoment H level δ s
  change g₁*c.regularizedProjectedLength H δ t+g₀*c.regularizedProjectedLength H δ s ≤ _
  linarith only [start,finish]

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.projectedHeight_separation
