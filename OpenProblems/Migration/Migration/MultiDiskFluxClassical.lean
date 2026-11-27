import Migration.MultiDiskFluxInitial
import Migration.MultiDiskFluxEarlier
import Migration.MultiDiskTurning
import Migration.MultiDiskBendingInvariant

noncomputable section
open Set
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable (c : SmoothPeriodicImmersion (Ioi 0))

private theorem multi_classical_bounds (hf : c.IsNormalFEF)
    (position : ContinuousOn (fun q : ℝ×ℝ=>c.position q.1 q.2) (Ici 0×ˢuniv))
    (spd : ContinuousOn (fun q : ℝ×ℝ=>speed (c.position q.1) q.2) (Ici 0×ˢuniv))
    (curv : ContinuousOn (fun q : ℝ×ℝ=>curvature (c.position q.1) q.2) (Ici 0×ˢuniv))
    (regular : ∀u,deriv (c.position 0) u≠0) {n : ℤ} (covers : 2≤|(n:ℝ)|)
    (turn : c.signedCurvatureIntegral 0=(n:ℝ)*(2*Real.pi))
    (initial : 2*c.bending 0*c.coreLength 0≤(2*Real.pi*|(n:ℝ)|)^2+Real.pi^2/4) :
    ContinuousWithinAt c.bending (Ici 0) 0 ∧ ContinuousWithinAt c.arclengthCentroid (Ici 0) 0 ∧
    0<c.bending 0 ∧ (∀v,0<v → |c.signedCurvatureIntegral v|=2*Real.pi*|(n:ℝ)|) ∧
    ∀v,0<v → 2*c.bending v*c.coreLength v≤(2*Real.pi*|(n:ℝ)|)^2+Real.pi^2/4 := by
  obtain ⟨en,len,cen,ep⟩:=c.multi_initial_material_limits hf position spd curv regular
  have all v (hv : 0<v) : |c.signedCurvatureIntegral v|=2*Real.pi*|(n:ℝ)| := by
    rw [c.multi_turn_from_zero spd curv turn hv.le,abs_mul,abs_of_pos (by positivity : 0<2*Real.pi),mul_comm]
  exact ⟨en,cen,ep,all,c.multi_bending_cap_from_zero hf covers ((en.const_mul 2).mul len) all initial⟩

/-- Persistent disk between any two times of the classical physical flow,
at every absolute covering number at least two. -/
theorem multi_classical_earlier_disk (hf : c.IsNormalFEF)
    (position : ContinuousOn (fun q : ℝ×ℝ=>c.position q.1 q.2) (Ici 0×ˢuniv))
    (spd : ContinuousOn (fun q : ℝ×ℝ=>speed (c.position q.1) q.2) (Ici 0×ˢuniv))
    (curv : ContinuousOn (fun q : ℝ×ℝ=>curvature (c.position q.1) q.2) (Ici 0×ˢuniv))
    (regular : ∀u,deriv (c.position 0) u≠0) {n : ℤ} (covers : 2≤|(n:ℝ)|)
    (turn : c.signedCurvatureIntegral 0=(n:ℝ)*(2*Real.pi))
    (initial : 2*c.bending 0*c.coreLength 0≤(2*Real.pi*|(n:ℝ)|)^2+Real.pi^2/4)
    {s t : ℝ} (hs : 0≤s) (st : s≤t) :
    let m:=|(n:ℝ)|
    Metric.closedBall (c.arclengthCentroid s)
      ((1+(1/m)^2/16)*((54/100)*(Real.pi*m)/c.bending s+(1/200)*(Real.pi*m)/c.bending t)) ⊆
        convexHull ℝ (c.position t '' Icc 0 c.period) := by
  obtain ⟨en,cen,ep,all,cap⟩:=c.multi_classical_bounds hf position spd curv regular covers turn initial
  exact c.multi_forward_earlier_disk_of_slabs hf covers position en cen ep all cap hs st

/-- A disk in the initial laboratory frame remains in every later convex hull. -/
theorem multi_classical_forward_disk (hf : c.IsNormalFEF)
    (position : ContinuousOn (fun q : ℝ×ℝ=>c.position q.1 q.2) (Ici 0×ˢuniv))
    (spd : ContinuousOn (fun q : ℝ×ℝ=>speed (c.position q.1) q.2) (Ici 0×ˢuniv))
    (curv : ContinuousOn (fun q : ℝ×ℝ=>curvature (c.position q.1) q.2) (Ici 0×ˢuniv))
    (regular : ∀u,deriv (c.position 0) u≠0) {n : ℤ} (covers : 2≤|(n:ℝ)|)
    (turn : c.signedCurvatureIntegral 0=(n:ℝ)*(2*Real.pi))
    (initial : 2*c.bending 0*c.coreLength 0≤(2*Real.pi*|(n:ℝ)|)^2+Real.pi^2/4)
    {t : ℝ} (ht : 0≤t) :
    let m:=|(n:ℝ)|
    Metric.closedBall (c.arclengthCentroid 0)
      ((1+(1/m)^2/16)*(109/200)*(Real.pi*m)/c.bending 0) ⊆
        convexHull ℝ (c.position t '' Icc 0 c.period) := by
  obtain ⟨en,cen,ep,all,cap⟩:=c.multi_classical_bounds hf position spd curv regular covers turn initial
  exact c.multi_forward_disk_of_slabs hf covers position en cen ep all cap ht

/-- Strict separation of two full traces forces initial excess greater than π²/4
at every absolute turning number at least two. -/
theorem multi_migration_requires_initial_excess (hf : c.IsNormalFEF)
    (position : ContinuousOn (fun q : ℝ×ℝ=>c.position q.1 q.2) (Ici 0×ˢuniv))
    (spd : ContinuousOn (fun q : ℝ×ℝ=>speed (c.position q.1) q.2) (Ici 0×ˢuniv))
    (curv : ContinuousOn (fun q : ℝ×ℝ=>curvature (c.position q.1) q.2) (Ici 0×ˢuniv))
    (regular : ∀u,deriv (c.position 0) u≠0) {n : ℤ} (covers : 2≤|(n:ℝ)|)
    (turn : c.signedCurvatureIntegral 0=(n:ℝ)*(2*Real.pi))
    {s t : ℝ} (hs : 0≤s) (ht : 0≤t)
    (migration : SimilarityHull.separated (c.position s '' Icc 0 c.period) (c.position t '' Icc 0 c.period)) :
    (2*Real.pi*|(n:ℝ)|)^2+Real.pi^2/4 < 2*c.bending 0*c.coreLength 0 := by
  by_contra! initial
  have r : 0≤(1+(1/|(n:ℝ)|)^2/16)*(109/200)*(Real.pi*|(n:ℝ)|)/c.bending 0 := by
    have en:=c.bending_nonneg 0;positivity
  have h:=Metric.mem_closedBall_self (x:=c.arclengthCentroid 0) r
  exact SimilarityHull.not_separated_of_common_hull
    (c.multi_classical_forward_disk hf position spd curv regular covers turn initial hs h)
    (c.multi_classical_forward_disk hf position spd curv regular covers turn initial ht h) migration

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.multi_classical_earlier_disk
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.multi_migration_requires_initial_excess

