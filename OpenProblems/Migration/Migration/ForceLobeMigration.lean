import Migration.ForceLobeSamples

noncomputable section
open Set MeasureTheory
namespace MigrationGeometry.Rotating.UnitLoop
variable {L : ℝ} (c : UnitLoop L)

/-- All pairs of similarity times are protected, including rotations between
the two slices, with no radius or bending threshold. -/
theorem no_migration_of_few_force_changes {m : ℕ} {a b : ℝ} (mp : 0<m) (ap : 0<a)
    (lp : 0<L) (sol : c.IsRotating a b) (turn : 2*Real.pi*(m:ℝ)≤|∫s in (0:ℝ)..L,c.k s|)
    (few : ¬c.alternatingForceVisits (2*m)) (v w : ℂ) :
    ¬SimilarityHull.separated (SimilarityHull.directSimilarity 0 v '' c.traceSet)
      (SimilarityHull.directSimilarity 0 w '' c.traceSet) := by
  have disk := c.centered_disk_of_signed_force_cover ap lp sol
    (c.signed_cover_of_few_force_changes mp lp turn few) (r:=0) (by simp)
  have origin : (0:ℂ)∈convexHull ℝ c.traceSet := disk (by simp)
  exact SimilarityHull.not_separated_of_common_hull (SimilarityHull.center_mem_direct_hull origin v)
    (SimilarityHull.center_mem_direct_hull origin w)

/-- The force-arc criterion allows zero total turning and self-intersections. -/
theorem no_migration_of_one_force_arc {a b s t : ℝ} (ap : 0<a) (lp : 0<L)
    (sol : c.IsRotating a b) (st : s≤t) (turn : 2*Real.pi≤|∫u in s..t,c.k u|)
    (side : (∀u∈Icc s t,0≤c.F u) ∨ (∀u∈Icc s t,c.F u≤0)) (v w : ℂ) :
    ¬SimilarityHull.separated (SimilarityHull.directSimilarity 0 v '' c.traceSet)
      (SimilarityHull.directSimilarity 0 w '' c.traceSet) := by
  have disk := c.centered_disk_of_one_force_arc ap lp sol st turn (f:=0) (by simpa using side)
    (r:=0) (by simp)
  have origin : (0:ℂ)∈convexHull ℝ c.traceSet := disk (by simp)
  exact SimilarityHull.not_separated_of_common_hull (SimilarityHull.center_mem_direct_hull origin v)
    (SimilarityHull.center_mem_direct_hull origin w)

end MigrationGeometry.Rotating.UnitLoop

#print axioms MigrationGeometry.Rotating.UnitLoop.no_migration_of_few_force_changes
#print axioms MigrationGeometry.Rotating.UnitLoop.no_migration_of_one_force_arc
