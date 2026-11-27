import Migration.SublevelInitialDisk
import Migration.SublevelReflection

noncomputable section
open Set MeasureTheory
open scoped ComplexConjugate
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem reflected_centroid {t : ℝ} (ht : t∈I) :
    c.reflected.arclengthCentroid t=conj (c.arclengthCentroid t) := by
  have sp (u) : speed (c.reflected.position t) u=speed (c.position t) u := by
    exact reflected_speed (c.position_slice_smooth ht) u
  unfold arclengthCentroid
  rw [c.reflected_length ht]
  have pos (u) : speed (c.reflected.position t) u • c.reflected.position t u=
      conj (speed (c.position t) u • c.position t u) := by
    rw [sp]
    simp [reflected,Complex.real_smul]
  rw [show c.reflected.period=c.period from rfl,funext pos]
  rw [intervalIntegral.intervalIntegral_conj]
  simp [Complex.real_smul]

theorem common_disk_from_initial_bending (hf : c.IsNormalFEF)
    {s t : ℝ} (st : s≤t) (slab : Icc s t⊆I)
    (initial : 2*c.bending s*c.coreLength s≤4*Real.pi^2+11/2) :
    Metric.closedBall (c.arclengthCentroid s)
      ((846/1000)*Real.pi/c.bending s+(4/1000)*Real.pi/c.bending t) ⊆
        convexHull ℝ (c.position t '' Icc 0 c.period) := by
  have hs := slab (show s∈Icc s t from ⟨le_rfl,st⟩)
  have ht := slab (show t∈Icc s t from ⟨st,le_rfl⟩)
  let p := c.materialSlice hs
  have en : p.bendingCurve.energy=c.bending s := p.bendingCurve_energy
  have leq : p.bendingCurve.period=c.coreLength s := rfl
  have cap : 2*p.bendingCurve.energy*p.bendingCurve.period≤4*Real.pi^2+36 := by
    rw [en,leq]; linarith only [initial]
  have turns := p.bendingCurve.low_product_turning cap
  have eq : (∫a in 0..p.bendingCurve.period,p.bendingCurve.curvature a)=c.signedCurvatureIntegral s := p.bendingCurve_turn
  rw [eq] at turns
  rcases turns with pos|neg
  · exact c.common_disk_from_positive_initial_data hf st slab (by rw [pos]; positivity) initial
  have init : 2*c.reflected.bending s*c.reflected.coreLength s≤4*Real.pi^2+11/2 := by
    rwa [c.reflected_length hs,c.reflected_bending hs]
  have disk := c.reflected.common_disk_from_positive_initial_data (c.reflected_flow hf) st slab
    (by rw [c.reflected_turn hs,neg]; linarith only [Real.pi_pos]) init
  rw [c.reflected_centroid hs,c.reflected_bending hs,c.reflected_bending ht] at disk
  intro z hz
  have dz := Complex.conjLIE.isometry.dist_eq z (c.arclengthCentroid s)
  have zz := disk (show conj z∈_ from Metric.mem_closedBall.mpr (dz.trans_le (Metric.mem_closedBall.mp hz)))
  let A : ℂ→ₗ[ℝ] ℂ := Complex.conjCLE.toLinearEquiv.toLinearMap
  have image_eq : c.reflected.position t '' Icc 0 c.period=A '' (c.position t '' Icc 0 c.period) := by
    rw [Set.image_image]
    rfl
  change conj z ∈convexHull ℝ (c.reflected.position t '' Icc 0 c.period) at zz
  rw [image_eq,← A.image_convexHull] at zz
  obtain ⟨v,hv,h⟩ := zz
  have hvz : v=z := Complex.conjCLE.injective h
  rwa [←hvz]

/-- The initial arclength barycentre stays in all future hulls. -/
theorem fixed_centroid_in_future_hull (hf : c.IsNormalFEF)
    {s t : ℝ} (st : s≤t) (slab : Icc s t⊆I)
    (initial : 2*c.bending s*c.coreLength s≤4*Real.pi^2+11/2) :
    c.arclengthCentroid s∈convexHull ℝ (c.position t '' Icc 0 c.period) := by
  apply c.common_disk_from_initial_bending hf st slab initial
  apply Metric.mem_closedBall_self
  have es := c.bending_nonneg s
  have et := c.bending_nonneg t
  positivity

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.fixed_centroid_in_future_hull
