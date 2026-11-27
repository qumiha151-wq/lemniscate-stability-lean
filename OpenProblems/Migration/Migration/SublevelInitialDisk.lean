import Migration.SublevelMaterialInvariant
import Migration.LowDefectMaterialSlab

noncomputable section
open Set MeasureTheory
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem scalar_turn_continuous_slab {s t : ℝ} (slab : Icc s t⊆I) :
    ContinuousOn c.signedCurvatureIntegral (Icc s t) := by
  apply continuousOn_intervalIntegral_of_isCompact isCompact_Icc
  exact (c.curvature_joint_smooth.continuousOn.mul c.speed_joint_smooth.continuousOn).mono
    (fun z hz=>⟨slab hz.1,mem_univ z.2⟩)

theorem common_disk_from_positive_initial_data (hf : c.IsNormalFEF)
    {s t : ℝ} (st : s≤t) (slab : Icc s t⊆I)
    (positive : 0<c.signedCurvatureIntegral s)
    (initial : 2*c.bending s*c.coreLength s≤4*Real.pi^2+11/2) :
    Metric.closedBall (c.arclengthCentroid s)
      ((846/1000)*Real.pi/c.bending s+(4/1000)*Real.pi/c.bending t) ⊆
        convexHull ℝ (c.position t '' Icc 0 c.period) := by
  have cap := c.bending_sublevel_from_initial hf st slab (C:=4*Real.pi^2+11/2)
      (by linarith) (by linarith) initial
  have winding (v) (hv : v∈Icc s t) :
      c.signedCurvatureIntegral v=2*Real.pi ∨ c.signedCurvatureIntegral v= -(2*Real.pi) := by
    let p := c.materialSlice (slab hv)
    have en : p.bendingCurve.energy=c.bending v := p.bendingCurve_energy
    have leq : p.bendingCurve.period=c.coreLength v := rfl
    have hh : 2*p.bendingCurve.energy*p.bendingCurve.period≤4*Real.pi^2+36 := by
      rw [en,leq]; linarith only [cap v hv]
    have turns := p.bendingCurve.low_product_turning hh
    have eq : (∫a in 0..p.bendingCurve.period,p.bendingCurve.curvature a)=c.signedCurvatureIntegral v := p.bendingCurve_turn
    rwa [eq] at turns
  apply c.common_disk_on_low_bending_slab hf st slab _ cap
  intro v hv
  rcases winding v hv with h|h
  · exact h
  · have sub : Icc s v⊆Icc s t := Icc_subset_Icc_right hv.2
    obtain ⟨x,hx,eq⟩ := intermediate_value_Icc' hv.1 ((c.scalar_turn_continuous_slab slab).mono sub)
      (show 0∈Icc (c.signedCurvatureIntegral v) (c.signedCurvatureIntegral s) from
        ⟨by rw [h]; linarith only [Real.pi_pos], positive.le⟩)
    rcases winding x (sub hx) with q|q <;> linarith only [q,eq,Real.pi_pos]

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.common_disk_from_positive_initial_data
