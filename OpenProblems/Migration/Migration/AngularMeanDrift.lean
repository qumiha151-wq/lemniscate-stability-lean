import Migration.AngularReconstruction

/-! Actual parameter-mean drift of the reconstructed projected position and
quantitative vertical errors for comparing a numerical trial with a chart. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace MigrationGeometry.AngularGauge

private theorem mean_from_spatial_derivative (P : ℝ) {g d : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt g (d x) x) (cd : Continuous d) :
    (∫ x in (0:ℝ)..P, g x) = P * g 0 + ∫ x in (0:ℝ)..P, (P-x)*d x := by
  have cg := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have cs : Continuous (fun x : ℝ => (P-x)*d x) := (continuous_const.sub continuous_id).mul cd
  have deriv (x : ℝ) : HasDerivAt (fun y => (P-y)*g y) ((P-x)*d x-g x) x := by
    apply (((hasDerivAt_const x P).sub (hasDerivAt_id x)).mul (hd x)).congr_deriv
    dsimp
    ring
  have eqn := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=P)
    (fun x _ => deriv x) ((cs.sub cg).intervalIntegrable ..)
  rw [intervalIntegral.integral_sub (cs.intervalIntegrable ..) (cg.intervalIntegrable ..)] at eqn
  simp only [sub_self, zero_mul, zero_sub, sub_zero] at eqn
  linarith only [eqn]

namespace Chart
variable {I : Set ℝ} {P : ℝ} (c : Chart I P)

def projectedMean (a b : ℝ) (anchor : ℝ → ℝ) (t : ℝ) :=
  (∫ x in (0:ℝ)..P, c.position a b anchor t x)/P

def projectedMeanSpeed (a b t : ℝ) :=
  c.rho t * (∫ x in (0:ℝ)..P, c.u t x * c.T a b t x)/P

private theorem slope_and_mixed_cont (a b : ℝ) :
    ContinuousOn (fun z : ℝ × ℝ => c.slope a b z.1 z.2) (I ×ˢ univ) ∧
    ContinuousOn (fun z : ℝ × ℝ => c.mixed a b z.1 z.2) (I ×ˢ univ) := by
  have rh : ContinuousOn (fun z : ℝ × ℝ => c.rho z.1) (I ×ˢ univ) :=
    c.rho_cont.comp continuous_fst.continuousOn (fun _ h => h.1)
  have ca : ContinuousOn (fun z : ℝ × ℝ => c.A z.1) (I ×ˢ univ) :=
    c.A_cont.comp continuous_fst.continuousOn (fun _ h => h.1)
  have ct : ContinuousOn (fun z : ℝ × ℝ => c.T a b z.1 z.2) (I ×ˢ univ) :=
    (continuousOn_const.mul (Real.continuous_cos.comp_continuousOn c.angle_cont)).add
      (continuousOn_const.mul (Real.continuous_sin.comp_continuousOn c.angle_cont))
  have cn : ContinuousOn (fun z : ℝ × ℝ => c.N a b z.1 z.2) (I ×ˢ univ) :=
    (continuousOn_const.mul (Real.continuous_sin.comp_continuousOn c.angle_cont)).add
      (continuousOn_const.mul (Real.continuous_cos.comp_continuousOn c.angle_cont))
  exact ⟨rh.mul ct, rh.mul ((ca.mul ct).add ((c.fx_cont.neg.add (c.u_cont.mul c.v_cont)).mul cn))⟩

private theorem onSlice {Q : ℝ → ℝ → ℝ} {t : ℝ} (ht : t∈I)
    (hq : ContinuousOn (fun z : ℝ × ℝ => Q z.1 z.2) (I ×ˢ univ)) :
    Continuous (Q t) :=
  continuousOn_univ.mp (hq.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ _ => ⟨ht,mem_univ _⟩))

/-- Spatial integration by parts reduces differentiation of the mean to a fixed
weighted integral of the slope. Only the anchor derivative at this time is needed. -/
theorem projectedMean_hasDerivAt (a b : ℝ) (anchor : ℝ → ℝ) {t : ℝ} (ht : t∈I)
    (ha : HasDerivAt anchor (c.velocity a b t 0) t) :
    HasDerivAt (c.projectedMean a b anchor) (c.projectedMeanSpeed a b t) t := by
  obtain ⟨cs,cm⟩ := c.slope_and_mixed_cont a b
  have sub : I ×ˢ uIcc 0 P ⊆ I ×ˢ (univ : Set ℝ) := fun _ h => ⟨h.1,mem_univ _⟩
  have weight : ContinuousOn (fun z : ℝ × ℝ => P-z.2) (I ×ˢ uIcc 0 P) :=
    (continuous_const.sub continuous_snd).continuousOn
  have hi := Flow.hasDerivAt_intervalIntegral_of_continuousOn (a:=0) (b:=P) c.openTime
    (weight.mul (cs.mono sub)) (weight.mul (cm.mono sub))
    (fun t ht s _ => (c.slope_time ht a b s).const_mul (P-s)) ht
  have heq : c.projectedMean a b anchor =ᶠ[𝓝 t] fun z =>
      (P*anchor z + ∫ x in (0:ℝ)..P, (P-x)*c.slope a b z x)/P := by
    filter_upwards [c.openTime.mem_nhds ht] with s hs
    have h := mean_from_spatial_derivative P (fun x => c.position_space hs a b x anchor) (onSlice hs cs)
    simpa only [projectedMean, position, intervalIntegral.integral_same, add_zero] using
      congrArg (fun r : ℝ => r/P) h
  have hm := mean_from_spatial_derivative P (fun x => c.velocity_space ht a b x) (onSlice ht cm)
  have hθ := onSlice ht c.angle_cont
  have cu := onSlice ht c.u_cont
  have ct : Continuous (c.T a b t) :=
    (continuous_const.mul (Real.continuous_cos.comp hθ)).add
      (continuous_const.mul (Real.continuous_sin.comp hθ))
  have cn : Continuous (c.N a b t) :=
    (continuous_const.mul (Real.continuous_sin.comp hθ)).add
      (continuous_const.mul (Real.continuous_cos.comp hθ))
  have cf : Continuous (c.f t) :=
    continuous_iff_continuousAt.mpr fun x => (c.force_x t ht x).continuousAt
  apply ((((ha.const_mul P).add hi).div_const P).congr_of_eventuallyEq heq).congr_deriv
  rw [← hm]
  simp only [velocity, projectedMeanSpeed, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub (f:=fun x => c.u t x*c.T a b t x)
    (g:=fun x => c.f t x*c.N a b t x)
    ((cu.mul ct).intervalIntegrable ..) ((cf.mul cn).intervalIntegrable ..),
    c.mean_normal_velocity_zero ht a b, sub_zero]

/-- Convert a difference of separately computed means into the spatial mean
of the error used by the height mesh enclosure. -/
theorem mesh_mean_difference {t : ℝ} (ht : t ∈ I) (a b : ℝ) (anchor Z : ℝ → ℝ)
    (cz : Continuous Z) :
    (∫ x in (0:ℝ)..P, (c.position a b anchor t-Z) x)/P =
      c.projectedMean a b anchor t-(∫ x in (0:ℝ)..P, Z x)/P := by
  have cy := continuous_iff_continuousAt.mpr
    (fun x => (c.position_space ht a b x anchor).continuousAt)
  change (∫ x in (0:ℝ)..P, c.position a b anchor t x-Z x)/P = _
  rw [intervalIntegral.integral_sub (f:=c.position a b anchor t) (g:=Z)
    (cy.intervalIntegrable ..) (cz.intervalIntegrable ..), sub_div, projectedMean]

end Chart

private theorem angle_sin_distance (x y : ℝ) : |Real.sin x-Real.sin y| ≤ |x-y| := by
  have h := (convex_univ (𝕜:=ℝ) (E:=ℝ)).norm_image_sub_le_of_norm_deriv_le
    (f:=Real.sin) (C:=1) (fun z _ => (Real.hasDerivAt_sin z).differentiableAt)
    (fun z _ => by rw [(Real.hasDerivAt_sin z).deriv]; exact Real.abs_cos_le_one z)
    (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs, one_mul] using h

/-- Vertical slope error with a nonnegative trial scale. -/
theorem vertical_slope_error (rho trial angle trialAngle : ℝ) (nonneg : 0 ≤ trial) :
    |rho*Real.sin angle-trial*Real.sin trialAngle| ≤
      |rho-trial|+trial*|angle-trialAngle| := by
  rw [show rho*Real.sin angle-trial*Real.sin trialAngle =
      (rho-trial)*Real.sin angle+trial*(Real.sin angle-Real.sin trialAngle) by ring]
  calc
    _ ≤ |(rho-trial)*Real.sin angle|+|trial*(Real.sin angle-Real.sin trialAngle)| := abs_add_le .. 
    _ = |rho-trial| * |Real.sin angle|+trial*|Real.sin angle-Real.sin trialAngle| := by
      rw [abs_mul (rho-trial), abs_mul trial, abs_of_nonneg nonneg]
    _ ≤ _ := by
      exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))
        (mul_le_mul_of_nonneg_left (angle_sin_distance ..) nonneg)

namespace Chart
variable {I : Set ℝ} {P : ℝ} (c : Chart I P)

theorem heightSlope_error {t x : ℝ} (R Θ : ℝ) (Rn : 0 ≤ R) :
    |c.slope 0 1 t x-R*Real.sin Θ| ≤ |c.rho t-R|+R*|c.theta t x-Θ| := by
  simpa only [slope, T, zero_mul, one_mul, zero_add] using
    vertical_slope_error (c.rho t) R (c.theta t x) Θ Rn

/-- A time-slice enclosure allowing independent errors in scale, angle and
tangential speed. All caps only need to hold on one spatial period. -/
theorem meanHeightSpeed_error {t : ℝ} (ht : t∈I) (pp : 0<P) (R : ℝ)
    (Θ U : ℝ → ℝ) (cnΘ : Continuous Θ) (cnU : Continuous U)
    (Rpos : 0≤R) {eR eΘ eU Umax : ℝ} (scale : |c.rho t-R|≤eR)
    (angle : ∀ x ∈ Icc 0 P, |c.theta t x-Θ x|≤eΘ)
    (drift : ∀ x ∈ Icc 0 P, |c.u t x-U x|≤eU)
    (umax : ∀ x ∈ Icc 0 P, |U x|≤Umax) :
    |c.projectedMeanSpeed 0 1 t -
      (∫ x in (0:ℝ)..P, U x*(R*Real.sin (Θ x)))/P| ≤
      c.rho t*eU+Umax*(eR+R*eΘ) := by
  let Y := fun x => c.u t x*(c.rho t*Real.sin (c.theta t x))
  let Z := fun x => U x*(R*Real.sin (Θ x))
  let C := c.rho t*eU+Umax*(eR+R*eΘ)
  have rn := (c.rho_pos t ht).le
  have cu := onSlice ht c.u_cont
  have ctheta := onSlice ht c.angle_cont
  have cy : Continuous Y := cu.mul ((Real.continuous_sin.comp ctheta).const_mul _)
  have cz : Continuous Z := cnU.mul ((Real.continuous_sin.comp cnΘ).const_mul _)
  have point (x : ℝ) (hx : x ∈ Icc 0 P) : |Y x-Z x|≤C := by
    have hs : |c.rho t*Real.sin (c.theta t x)-R*Real.sin (Θ x)|≤eR+R*eΘ :=
      (vertical_slope_error _ _ _ _ Rpos).trans
        (add_le_add scale (mul_le_mul_of_nonneg_left (angle x hx) Rpos))
    have sy : |c.rho t*Real.sin (c.theta t x)|≤c.rho t := by
      rw [abs_mul, abs_of_nonneg rn]
      exact mul_le_of_le_one_right rn (Real.abs_sin_le_one _)
    have id : Y x-Z x = (c.u t x-U x)*(c.rho t*Real.sin (c.theta t x))+
        U x*(c.rho t*Real.sin (c.theta t x)-R*Real.sin (Θ x)) := by dsimp [Y,Z]; ring
    rw [id]
    apply (abs_add_le ..).trans
    rw [abs_mul (c.u t x-U x), abs_mul (U x)]
    dsimp only [C]
    rw [mul_comm (c.rho t) eU]
    exact add_le_add (mul_le_mul (drift x hx) sy (abs_nonneg _) ((abs_nonneg _).trans (drift x hx)))
      (mul_le_mul (umax x hx) hs (abs_nonneg _) ((abs_nonneg _).trans (umax x hx)))
  have hi := (intervalIntegral.abs_integral_le_integral_abs (μ:=volume)
    (f:=fun x => Y x-Z x) pp.le).trans
    (intervalIntegral.integral_mono_on (μ:=volume) pp.le ((cy.sub cz).abs.intervalIntegrable ..)
      (g:=fun _ => C) intervalIntegrable_const point)
  rw [intervalIntegral.integral_sub (f:=Y) (g:=Z) (μ:=volume) (a:=0) (b:=P)
    (cy.intervalIntegrable ..) (cz.intervalIntegrable ..),
    intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hi
  have rearr : c.projectedMeanSpeed 0 1 t = (∫ x in (0:ℝ)..P, Y x)/P := by
    simp only [projectedMeanSpeed, T, zero_mul, one_mul, zero_add]
    simp_rw [show ∀ x, Y x=c.rho t*(c.u t x*Real.sin (c.theta t x)) from fun x => by dsimp [Y]; ring]
    rw [intervalIntegral.integral_const_mul]
  rw [rearr, ← sub_div, abs_div, abs_of_pos pp]
  apply (div_le_iff₀ pp).mpr
  exact hi.trans_eq (mul_comm _ _)

end Chart

/-- Propagate a mean-height error from one time section to the next using a
bound on the discrepancy of the two mean velocities. -/
theorem propagate_mean_error {g q g' q' : ℝ → ℝ} {s t V A : ℝ} (st : s≤t)
    (dg : ∀ u ∈ Icc s t, HasDerivAt g (g' u) u)
    (dq : ∀ u ∈ Icc s t, HasDerivAt q (q' u) u)
    (dv : ∀ u ∈ Icc s t, |g' u-q' u|≤V) (initial : |g s-q s|≤A) :
    |g t-q t| ≤ A+V*(t-s) := by
  have h := (convex_Icc s t).norm_image_sub_le_of_norm_deriv_le
    (f:=g-q) (C:=V) (fun u hu => ((dg u hu).sub (dq u hu)).differentiableAt)
    (fun u hu => by rw [((dg u hu).sub (dq u hu)).deriv]; exact dv u hu)
    (left_mem_Icc.mpr st) (right_mem_Icc.mpr st)
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr st)] at h
  calc
    _ = |(g s-q s)+((g t-q t)-(g s-q s))| := by ring_nf
    _ ≤ _ := (abs_add_le ..).trans (add_le_add initial h)

end MigrationGeometry.AngularGauge
#print axioms MigrationGeometry.AngularGauge.Chart.projectedMean_hasDerivAt
#print axioms MigrationGeometry.AngularGauge.Chart.meanHeightSpeed_error
#print axioms MigrationGeometry.AngularGauge.propagate_mean_error

