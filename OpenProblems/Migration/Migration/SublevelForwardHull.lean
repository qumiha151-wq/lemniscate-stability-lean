import Migration.SublevelForwardLimit
import Mathlib.Topology.Order.Compact

noncomputable section
open Set Filter
open scoped Topology
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable (c : SmoothPeriodicImmersion (Ioi 0))

private theorem initial_hull_of_later_membership
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

/-- The initial curve and every positive-time curve have an explicit
common disk even when smooth time evolution is only specified for t>0. -/
theorem forward_all_hulls_common_disk (hf : c.IsNormalFEF)
    (position : ContinuousOn (fun q : ℝ×ℝ=>c.position q.1 q.2) (Ici 0×ˢuniv))
    (energy : ContinuousWithinAt c.bending (Ici 0) 0)
    (len : ContinuousWithinAt c.coreLength (Ici 0) 0)
    (center : ContinuousWithinAt c.arclengthCentroid (Ici 0) 0)
    (ep : 0<c.bending 0)
    (initial : 2*c.bending 0*c.coreLength 0≤4*Real.pi^2+11/2)
    {t : ℝ} (ht : 0≤t) :
    Metric.closedBall (c.arclengthCentroid 0) ((85/100)*Real.pi/c.bending 0) ⊆
      convexHull ℝ (c.position t '' Icc 0 c.period) := by
  intro z hz
  have later (v : ℝ) (hv : 0<v) := c.forward_persistent_disk hf energy len center ep initial hv hz
  rcases eq_or_lt_of_le ht with rfl|pos
  · exact c.initial_hull_of_later_membership position later
  · exact later t pos

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.forward_all_hulls_common_disk
