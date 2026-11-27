import Migration.NearRoundDisk

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff

namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

/-- Variance of the actual normal/curvature field in the chosen direction. -/
def centroidFluxMoment (H : ℂ →L[ℝ] ℝ) (t : ℝ) : ℝ :=
  ∫ u in 0..c.period,
    (curvature (c.position t) u * (H (c.position t u) - c.centroidHeight H t) +
      H (normal (c.position t) u))^2 * speed (c.position t) u

/-- The centroid force derivative is bounded by a spatial geometric moment
of the same physical curve times its true dissipation. -/
theorem centroidRate_le_flux_moment (H : ℂ →L[ℝ] ℝ) {t : ℝ} (ht : t ∈ I) :
    |c.centroidRate H t| * c.coreLength t ≤
      Real.sqrt (c.centroidFluxMoment H t) *
        Real.sqrt (c.localDissipation H (fun _ => 1) t) := by
  let γ := c.position t
  let F := force γ
  let g := speed γ
  let Q := fun u => curvature γ u * (H (γ u)-c.centroidHeight H t)+H (normal γ u)
  have hγ := c.position_slice_smooth ht
  have hreg := c.immersion t ht
  have gp (u) : 0 ≤ g u := (speed_pos hreg u).le
  have cf := (force_smooth hγ hreg).continuous
  have cg := (speed_smooth hγ hreg).continuous
  have cq : Continuous Q := ((curvature_smooth hγ hreg).continuous.mul
    ((H.continuous.comp hγ.continuous).sub continuous_const)).add
      (H.continuous.comp (normal_smooth hγ hreg).continuous)
  have hd := weighted_abs_force c.period_pos.le cq cf cg gp
  have he : (∫ u in 0..c.period, F u^2*g u) =
      c.localDissipation H (fun _ => 1) t := by simp [F, g, γ, localDissipation]
  rw [← he]
  change |(∫ u in 0..c.period,Q u*F u*g u)/c.coreLength t| * c.coreLength t ≤ _
  rw [abs_div,abs_of_pos (c.coreLength_pos ht),div_mul_cancel₀ _ (c.coreLength_pos ht).ne']
  apply (intervalIntegral.abs_integral_le_integral_abs c.period_pos.le).trans
  apply le_trans _ hd
  apply le_of_eq
  apply intervalIntegral.integral_congr
  intro u _
  change |Q u*F u*g u| = |Q u| * |F u| * g u
  rw [abs_mul,abs_mul,abs_of_nonneg (gp u)]

/-- Spatial squared normal support moment in material coordinates. -/
def centeredSupportMoment (t : ℝ) : ℝ :=
  ∫ u in 0..c.period,
    (inner ℝ (normal (c.position t) u) (c.position t u - c.arclengthCentroid t))^2 *
      speed (c.position t) u

/-- Cauchy--Schwarz applied to the exact material dilation virial. -/
theorem bending_le_support_moment (H : ℂ →L[ℝ] ℝ) {t : ℝ} (ht : t ∈ I) :
    c.bending t ≤ Real.sqrt (c.centeredSupportMoment t) *
      Real.sqrt (c.localDissipation H (fun _ => 1) t) := by
  let γ := c.position t
  let F := force γ
  let g := speed γ
  let p := fun u => inner ℝ (normal γ u) (γ u-c.arclengthCentroid t)
  have hγ := c.position_slice_smooth ht
  have hreg := c.immersion t ht
  have gp (u) : 0 ≤ g u := (speed_pos hreg u).le
  have cp : Continuous p := (normal_smooth hγ hreg).continuous.inner
    (hγ.continuous.sub continuous_const)
  have hd := weighted_abs_force c.period_pos.le cp (force_smooth hγ hreg).continuous
    (speed_smooth hγ hreg).continuous gp
  have he : (∫ u in 0..c.period, F u^2*g u) =
      c.localDissipation H (fun _ => 1) t := by simp [F,g,γ,localDissipation]
  rw [← he]
  have hv := c.material_virial ht (c.arclengthCentroid t)
  change (∫ u in 0..c.period, g u * F u * p u) = -c.bending t at hv
  have e : c.bending t = |∫ u in 0..c.period, g u * F u * p u| := by
    rw [hv,abs_neg,abs_of_nonneg (c.bending_nonneg t)]
  rw [e]
  apply (intervalIntegral.abs_integral_le_integral_abs c.period_pos.le).trans
  apply le_trans _ hd
  apply le_of_eq
  apply intervalIntegral.integral_congr
  intro u _
  change |g u*F u*p u| = |p u| * |F u| * g u
  rw [abs_mul,abs_mul,abs_of_nonneg (gp u)]
  ring

private theorem moment_rate {E L J M D K : ℝ} (e : 0 < E) (l : 0 < L) (d : 0 ≤ D)
    {b : ℝ} (cb : b*L ≤ Real.sqrt M * Real.sqrt D)
    (ev : E ≤ Real.sqrt J * Real.sqrt D)
    (budget : E * Real.sqrt M * Real.sqrt J ≤ K*L) :
    b ≤ K*D / E^2 := by
  have h := mul_le_mul cb ev e.le (by positivity)
  have h' := mul_le_mul_of_nonneg_right budget d
  have deq : Real.sqrt M * Real.sqrt D * (Real.sqrt J * Real.sqrt D) =
      Real.sqrt M * Real.sqrt J * D := by
    calc
      _ = Real.sqrt M * Real.sqrt J * (Real.sqrt D)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt d]
  rw [deq] at h
  have hn := mul_le_mul_of_nonneg_left h e.le
  apply (le_div_iff₀ (sq_pos_of_pos e)).mpr
  apply (mul_le_mul_iff_left₀ l).mp
  nlinarith only [hn,h']

/-- Converts snapshot force moments and support estimates into a common
physical disk. No time-integrated drift or velocity estimate is an input. -/
theorem earlier_ball_of_spatial_flux_moments (hf : c.IsNormalFEF)
    {s t α β : ℝ} (hst : s ≤ t) (slab : Icc s t ⊆ I)
    (energy : ∀ v ∈ Icc s t, 0 < c.bending v)
    (budget : ∀ e : ℂ, ‖e‖ = 1 → ∀ v ∈ Icc s t,
      c.bending v * Real.sqrt (c.centroidFluxMoment (innerSL ℝ e) v) *
        Real.sqrt (c.centeredSupportMoment v) ≤ α*c.coreLength v)
    (support : ∀ e : ℂ, ‖e‖ = 1 → ∃ u ∈ Icc 0 c.period,
      inner ℝ e (c.arclengthCentroid t) + β/c.bending t ≤ inner ℝ e (c.position t u))
    {r : ℝ} (rad : r < α/c.bending s + (β-α)/c.bending t) :
    Metric.closedBall (c.arclengthCentroid s) r ⊆
      convexHull ℝ (c.position t '' Icc 0 c.period) := by
  apply closedBall_subset_convexHull_of_directional_margin rad
  intro e he
  let H := innerSL ℝ e
  have rate (v) (hv : v ∈ Icc s t) :
      |c.centroidRate H v| ≤ α*c.localDissipation H (fun _ => 1) v / c.bending v^2 := by
    have hd : 0 ≤ c.localDissipation H (fun _ => 1) v :=
      intervalIntegral.integral_nonneg_of_forall c.period_pos.le
        (fun u => mul_nonneg (sq_nonneg _) (speed_pos (c.immersion v (slab hv)) u).le)
    exact moment_rate (energy v hv) (c.coreLength_pos (slab hv)) hd
      (c.centroidRate_le_flux_moment H (slab hv)) (c.bending_le_support_moment H (slab hv))
      (budget e he v hv)
  have drift := c.centroid_displacement_of_force_bound hf H hst slab energy rate
  rw [← c.map_arclengthCentroid H (slab ⟨hst,le_rfl⟩),
      ← c.map_arclengthCentroid H (slab ⟨le_rfl,hst⟩)] at drift
  change |inner ℝ e (c.arclengthCentroid t)-inner ℝ e (c.arclengthCentroid s)| ≤ _ at drift
  obtain ⟨u,hu,hs⟩ := support e he
  refine ⟨c.position t u,⟨u,hu,rfl⟩,?_⟩
  rw [sub_div]
  linarith [(abs_le.mp drift).1]

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.earlier_ball_of_spatial_flux_moments
