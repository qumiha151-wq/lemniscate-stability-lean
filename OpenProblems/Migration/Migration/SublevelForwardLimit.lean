import Migration.SublevelFixedRadius
import Migration.SimilarityHull

noncomputable section
open Set Filter
open scoped Topology
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable (c : SmoothPeriodicImmersion (Ioi 0))

/-- The cap is allowed to hold with equality at a one-sided starting time.
The proof perturbs the threshold rather than assuming an initial derivative. -/
theorem forward_bending_cap (hf : c.IsNormalFEF)
    (energy : ContinuousWithinAt c.bending (Ici 0) 0)
    (len : ContinuousWithinAt c.coreLength (Ici 0) 0)
    (initial : 2*c.bending 0*c.coreLength 0≤4*Real.pi^2+11/2)
    {t : ℝ} (ht : 0<t) : 2*c.bending t*c.coreLength t≤4*Real.pi^2+11/2 := by
  let U := fun t=>2*c.bending t*c.coreLength t
  let C := 4*Real.pi^2+11/2
  let cap := 4*Real.pi^2+36
  have cu : ContinuousWithinAt U (Ioi 0) 0 :=
    ((energy.const_mul 2).mul len).mono Ioi_subset_Ici_self
  by_contra! high
  have hhigh : C<U t := high
  have hh : C<cap := by dsimp [C,cap]; linarith
  let M := (C+min (U t) cap)/2
  have greater : C<M := by dsimp only [M]; linarith only [lt_min hhigh hh]
  have smaller : M<min (U t) cap := by dsimp only [M]; linarith only [lt_min hhigh hh]
  have threshold := cu.eventually_lt_const (lt_of_le_of_lt initial greater)
  have time : ∀ᶠ v in 𝓝[>] (0:ℝ), v<t := (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds ht)
  have after : ∀ᶠ v in 𝓝[>] (0:ℝ), 0<v := self_mem_nhdsWithin
  obtain ⟨v,hv,vt,hvM⟩ := (after.and (time.and threshold)).exists
  have slab : Icc v t⊆Ioi 0 := fun x hx=>lt_of_lt_of_le hv hx.1
  have above : 4*Real.pi^2<M := by dsimp [C] at greater; linarith
  have bd := c.bending_sublevel_from_initial hf vt.le slab above
    (smaller.le.trans (min_le_right _ _)) hvM.le t ⟨vt.le,le_rfl⟩
  exact (not_lt_of_ge bd) (smaller.trans_le (min_le_left _ _))

/-- For a one-sided flow on positive time, every positive-time hull contains
the fixed physical disk based at the initial curve's arclength barycentre. -/
theorem forward_persistent_disk (hf : c.IsNormalFEF)
    (energy : ContinuousWithinAt c.bending (Ici 0) 0)
    (len : ContinuousWithinAt c.coreLength (Ici 0) 0)
    (center : ContinuousWithinAt c.arclengthCentroid (Ici 0) 0)
    (ep : 0<c.bending 0)
    (initial : 2*c.bending 0*c.coreLength 0≤4*Real.pi^2+11/2)
    {t : ℝ} (ht : 0<t) :
    Metric.closedBall (c.arclengthCentroid 0) ((85/100)*Real.pi/c.bending 0) ⊆
      convexHull ℝ (c.position t '' Icc 0 c.period) := by
  let K := convexHull ℝ (c.position t '' Icc 0 c.period)
  have compact : IsCompact K := MigrationGeometry.SimilarityHull.compact_convexHull
      (isCompact_Icc.image (c.position_slice_smooth ht).continuous)
  intro z hz
  let z' := fun v=>c.arclengthCentroid v+(c.bending 0/c.bending v) • (z-c.arclengthCentroid 0)
  have inc : Ioi (0:ℝ)⊆Ici 0 := Ioi_subset_Ici_self
  have cl : Tendsto z' (𝓝[>] 0) (𝓝 z) := by
    have h := (center.mono inc).tendsto.add (((tendsto_const_nhds (x:=c.bending 0)).div
       (energy.mono inc).tendsto ep.ne').smul (tendsto_const_nhds (x:=z-c.arclengthCentroid 0)))
    simpa [z',div_self ep.ne'] using h
  apply compact.isClosed.mem_of_tendsto cl
  have time : ∀ᶠ v in 𝓝[>] (0:ℝ), v<t := (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds ht)
  filter_upwards [self_mem_nhdsWithin,time] with v (hv : 0<v) vt
  have ev := c.bending_pos_of_width hv
  apply c.persistent_disk_from_initial_bending hf vt.le (fun x hx=>lt_of_lt_of_le hv hx.1)
    (c.forward_bending_cap hf energy len initial hv)
  rw [Metric.mem_closedBall,dist_eq_norm] at hz ⊢
  dsimp only [z']
  rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos ep ev)]
  calc c.bending 0 / c.bending v * ‖z-c.arclengthCentroid 0‖ ≤
      c.bending 0/c.bending v * ((85/100)*Real.pi/c.bending 0) :=
        mul_le_mul_of_nonneg_left hz (div_pos ep ev).le
    _ = _ := by field_simp [ep.ne']

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.forward_persistent_disk
