import Migration.SublevelForwardGeometry
import Migration.EscapingHulls

noncomputable section
open Set
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable (c : SmoothPeriodicImmersion (Ioi 0))

/-- If two material traces of a classical forward flow lie in opposite
open half-planes, its initial normalized bending energy exceeds this floor. -/
theorem migration_requires_initial_bending (hf : c.IsNormalFEF)
    (position : ContinuousOn (fun q : ℝ×ℝ=>c.position q.1 q.2) (Ici 0×ˢuniv))
    (spd : ContinuousOn (fun q : ℝ×ℝ=>speed (c.position q.1) q.2) (Ici 0×ˢuniv))
    (curv : ContinuousOn (fun q : ℝ×ℝ=>curvature (c.position q.1) q.2) (Ici 0×ˢuniv))
    (regular : ∀u,deriv (c.position 0) u≠0)
    {s t : ℝ} (hs : 0≤s) (ht : 0≤t)
    (migration : SimilarityHull.separated (c.position s '' Icc 0 c.period) (c.position t '' Icc 0 c.period)) :
    4*Real.pi^2+11/2 < 2*c.bending 0*c.coreLength 0 := by
  by_contra! initial
  have hrad : 0≤(85/100)*Real.pi/c.bending 0 := by
    have := c.bending_nonneg 0
    positivity
  have center := Metric.mem_closedBall_self (x:=c.arclengthCentroid 0) hrad
  exact SimilarityHull.not_separated_of_common_hull
    (c.classical_forward_initial_disk hf position spd curv regular initial hs center)
    (c.classical_forward_initial_disk hf position spd curv regular initial ht center) migration

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.migration_requires_initial_bending
