import Migration.MultiDiskFluxActual
import Migration.SublevelForwardGeometry

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem multi_fixed_disk_on_abs_bending_slab (hf : c.IsNormalFEF) {m s t : ℝ} (hm : 2≤m)
    (st : s≤t) (slab : Icc s t⊆I) (turn : ∀v∈Icc s t,|c.signedCurvatureIntegral v|=2*Real.pi*m)
    (energy : ∀v∈Icc s t,2*c.bending v*c.coreLength v≤(2*Real.pi*m)^2+Real.pi^2/4) :
    Metric.closedBall (c.arclengthCentroid s)
      ((1+(1/m)^2/16)*(109/200)*(Real.pi*m)/c.bending s) ⊆
        convexHull ℝ (c.position t '' Icc 0 c.period) := by
  have main:=c.multi_disk_on_abs_bending_slab hf hm st slab turn energy
  apply (Metric.closedBall_subset_closedBall ?_).trans main
  have mp : 0<m := by linarith
  have pos := c.bending_pos_of_width (slab (show t∈Icc s t from ⟨st,le_rfl⟩))
  have leq := c.bending_le_of_slab hf Complex.reCLM st slab
  have leR:=div_le_div_of_nonneg_left (show 0≤(1/200)*(Real.pi*m) by positivity) pos leq
  have upper:=mul_le_mul_of_nonneg_left leR (show 0≤1+(1/m)^2/16 by positivity)
  linarith only [upper,show (1+(1/m)^2/16)*(109/200)*(Real.pi*m)/c.bending s=
    (1+(1/m)^2/16)*((54/100)*(Real.pi*m)/c.bending s)+(1+(1/m)^2/16)*((1/200)*(Real.pi*m)/c.bending s) by ring,
    show (1+(1/m)^2/16)*((54/100)*(Real.pi*m)/c.bending s+(1/200)*(Real.pi*m)/c.bending t)=
    (1+(1/m)^2/16)*((54/100)*(Real.pi*m)/c.bending s)+(1+(1/m)^2/16)*((1/200)*(Real.pi*m)/c.bending t) by ring]

end MigrationGeometry.Flow.SmoothPeriodicImmersion
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable (c : SmoothPeriodicImmersion (Ioi 0))

theorem multi_initial_hull_of_later_membership
    (position : ContinuousOn (fun q : ℝ×ℝ=>c.position q.1 q.2) (Ici 0×ˢuniv))
    {z : ℂ} (later : ∀v : ℝ, 0<v → z∈convexHull ℝ (c.position v '' Icc 0 c.period)) :
    z∈convexHull ℝ (c.position 0 '' Icc 0 c.period) := by
  have jc : Continuous (fun q : ℝ×ℝ=>c.position (max q.1 0) q.2) :=
    position.comp_continuous ((continuous_fst.max continuous_const).prodMk continuous_snd)
      (fun q=>⟨show 0≤max q.1 0 from le_max_right _ _,mem_univ _⟩)
  have zero : Continuous (c.position 0) := by
    simpa [Function.comp_def] using jc.comp ((continuous_const :
      Continuous (fun _ : ℝ=>(0:ℝ))).prodMk continuous_id)
  let K := c.position 0 '' Icc 0 c.period
  by_contra out
  obtain ⟨H,r,low,high⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ K)
    (MigrationGeometry.SimilarityHull.compact_convexHull (isCompact_Icc.image zero)).isClosed out
  let f := fun (v u : ℝ)=>H (c.position (max v 0) u)
  let supAt := fun v=>sSup (f v '' Icc 0 c.period)
  have cf : Continuous (Function.uncurry f) := H.continuous.comp jc
  have cs : Continuous supAt := isCompact_Icc.continuous_sSup cf
  have maxpt (v : ℝ) := isCompact_Icc.exists_sSup_image_eq_and_ge
    (show (Icc (0:ℝ) c.period).Nonempty from ⟨0,le_rfl,c.period_pos.le⟩)
    (show Continuous (f v) from cf.comp (.prodMk_right v)).continuousOn
  have now : supAt 0<r := by
    obtain ⟨u,hu,h,_⟩ := maxpt 0
    change sSup (f 0 '' Icc 0 c.period)<r
    rw [h]
    simpa [f] using low (c.position 0 u) (subset_convexHull ℝ K ⟨u,hu,rfl⟩)
  have ev : ∀ᶠ v in 𝓝[>] (0:ℝ), H z≤supAt v := by
    filter_upwards [self_mem_nhdsWithin] with v (hv : 0<v)
    let B := {w : ℂ | H w≤supAt v}
    have cap : c.position v '' Icc 0 c.period ⊆ B := by
      rintro _ ⟨u,hu,rfl⟩
      obtain ⟨y,_,eq,m⟩ := maxpt v
      change H (c.position v u)≤sSup (f v '' Icc 0 c.period)
      rw [eq]
      simpa [f,max_eq_left hv.le] using m u hu
    exact (convexHull_min cap (convex_halfSpace_le H.toLinearMap.isLinear _)) (later v hv)
  have hz := le_of_tendsto_of_tendsto tendsto_const_nhds
    (cs.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ev
  linarith


/-- One-sided continuity passes the common disk from all positive-time slices to
the initial lab frame. The time-zero evolution equation is unnecessary. -/
theorem multi_forward_disk_of_slabs (hf : c.IsNormalFEF) {m : ℝ} (hm : 2≤m)
    (position : ContinuousOn (fun q : ℝ×ℝ=>c.position q.1 q.2) (Ici 0×ˢuniv))
    (energy : ContinuousWithinAt c.bending (Ici 0) 0)
    (center : ContinuousWithinAt c.arclengthCentroid (Ici 0) 0)
    (ep : 0<c.bending 0)
    (turn : ∀v,0<v → |c.signedCurvatureIntegral v|=2*Real.pi*m)
    (cap : ∀v,0<v → 2*c.bending v*c.coreLength v≤(2*Real.pi*m)^2+Real.pi^2/4)
    {t : ℝ} (ht : 0≤t) :
    Metric.closedBall (c.arclengthCentroid 0) ((1+(1/m)^2/16)*(109/200)*(Real.pi*m)/c.bending 0) ⊆
        convexHull ℝ (c.position t '' Icc 0 c.period) := by
  intro z hz
  have later (r : ℝ) (hr : 0<r) : z∈convexHull ℝ (c.position r '' Icc 0 c.period) := by
    let K:=convexHull ℝ (c.position r '' Icc 0 c.period)
    have compact : IsCompact K := MigrationGeometry.SimilarityHull.compact_convexHull
      (isCompact_Icc.image (c.position_slice_smooth hr).continuous)
    let zz:=fun v=>c.arclengthCentroid v+(c.bending 0/c.bending v) • (z-c.arclengthCentroid 0)
    have inc : Ioi (0:ℝ)⊆Ici 0 := Ioi_subset_Ici_self
    have conv : Tendsto zz (𝓝[>] 0) (𝓝 z) := by
      have h:=(center.mono inc).tendsto.add (((tendsto_const_nhds (x:=c.bending 0)).div
         (energy.mono inc).tendsto ep.ne').smul (tendsto_const_nhds (x:=z-c.arclengthCentroid 0)))
      simpa [zz,div_self ep.ne'] using h
    apply compact.isClosed.mem_of_tendsto conv
    have time : ∀ᶠ v in 𝓝[>] (0:ℝ), v<r := (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hr)
    filter_upwards [self_mem_nhdsWithin,time] with v (hv : 0<v) vr
    have ev:=c.bending_pos_of_width hv
    have sub : Icc v r⊆Ioi 0 := fun y hy=>lt_of_lt_of_le hv hy.1
    apply c.multi_fixed_disk_on_abs_bending_slab hf hm vr.le sub (fun y hy=>turn y (sub hy)) (fun y hy=>cap y (sub hy))
    rw [Metric.mem_closedBall,dist_eq_norm] at hz ⊢
    dsimp only [zz]
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos ep ev)]
    apply (mul_le_mul_of_nonneg_left hz (div_pos ep ev).le).trans_eq
    field_simp [ep.ne']
  rcases eq_or_lt_of_le ht with rfl|pos
  · exact c.multi_initial_hull_of_later_membership position later
  · exact later t pos

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.multi_forward_disk_of_slabs

