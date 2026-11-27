import Migration.DirectionalWidth
import Migration.SublevelPhysicalDisk

noncomputable section
open Set MeasureTheory
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

/-- A disk of fixed positive radius, in the initial laboratory frame, belongs to
all subsequent hulls. The radius uses only the earlier curve's bending energy. -/
theorem persistent_disk_from_initial_bending (hf : c.IsNormalFEF)
    {s t : ℝ} (st : s≤t) (slab : Icc s t⊆I)
    (initial : 2*c.bending s*c.coreLength s≤4*Real.pi^2+11/2) :
    Metric.closedBall (c.arclengthCentroid s) ((85/100)*Real.pi/c.bending s) ⊆
        convexHull ℝ (c.position t '' Icc 0 c.period) := by
  apply Set.Subset.trans (Metric.closedBall_subset_closedBall ?_) (c.common_disk_from_initial_bending hf st slab initial)
  have pos := c.bending_pos_of_width (slab (show t∈Icc s t from ⟨st,le_rfl⟩))
  have leq := c.bending_le_of_slab hf Complex.reCLM st slab
  have h := div_le_div_of_nonneg_left (show 0≤(4/1000)*Real.pi by positivity) pos leq
  calc (85/100)*Real.pi/c.bending s =
      (846/1000)*Real.pi/c.bending s + (4/1000)*Real.pi/c.bending s := by ring
    _ ≤ _ := add_le_add_right h _

theorem later_hulls_share_initial_disk (hf : c.IsNormalFEF) {s t₁ t₂ : ℝ}
    (h₁ : s≤t₁) (h₂ : s≤t₂) (slab₁ : Icc s t₁⊆I) (slab₂ : Icc s t₂⊆I)
    (initial : 2*c.bending s*c.coreLength s≤4*Real.pi^2+11/2) :
    Metric.closedBall (c.arclengthCentroid s) ((85/100)*Real.pi/c.bending s) ⊆
      (convexHull ℝ (c.position t₁ '' Icc 0 c.period)) ∩
      (convexHull ℝ (c.position t₂ '' Icc 0 c.period)) :=
  Set.subset_inter (c.persistent_disk_from_initial_bending hf h₁ slab₁ initial)
    (c.persistent_disk_from_initial_bending hf h₂ slab₂ initial)

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.later_hulls_share_initial_disk
