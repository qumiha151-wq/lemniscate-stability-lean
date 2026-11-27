import Migration.LowDefectMaterialFlux
import Migration.LowDefectPhysicalSupport

noncomputable section
open Set MeasureTheory
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

/-- Genuine physical non-migration on every slab in the one-turn low bending
sublevel. No spatial Fourier bounds, support assumptions, force budgets or
centroid mobility estimates have to be supplied. -/
theorem common_disk_on_low_bending_slab (hf : c.IsNormalFEF)
    {s t : ℝ} (st : s≤t) (slab : Icc s t⊆I)
    (turn : ∀v∈Icc s t,c.signedCurvatureIntegral v=2*Real.pi)
    (energy : ∀v∈Icc s t,2*c.bending v*c.coreLength v≤4*Real.pi^2+11/2) :
    Metric.closedBall (c.arclengthCentroid s)
      ((846/1000)*Real.pi/c.bending s+(4/1000)*Real.pi/c.bending t) ⊆
        convexHull ℝ (c.position t '' Icc 0 c.period) := by
  let D := fun v => c.curvatureOscillation (2*Real.pi) v/(2*Real.pi)^2
  let x := fun v => Real.sqrt (D v)
  have pos (v) (hv : v∈Icc s t) : 0≤D v := div_nonneg (c.curvatureOscillation_nonneg (slab hv) _) (sq_nonneg _)
  have lim (v) (hv : v∈Icc s t) : D v ≤ (374/1000)^2 := by
    have eq := c.oscillation_energy_identity (slab hv) (turn v hv)
    have en := energy v hv
    have d : c.curvatureOscillation (2*Real.pi) v≤11/2 := by nlinarith only [eq,en]
    change _/(2*Real.pi)^2≤_
    rw [div_le_iff₀ (by positivity)]
    have p := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3.14) Real.pi_gt_d2.le 2
    nlinarith only [p,d]
  have small (v) (hv : v∈Icc s t) : D v≤14/100 := (lim v hv).trans (by norm_num)
  have sq (v) (hv : v∈Icc s t) : x v^2=D v := Real.sq_sqrt (pos v hv)
  apply c.physical_disk_of_fourier_estimates hf st slab x (fun _ _=>Real.sqrt_nonneg _)
    (fun v hv=>(Real.sqrt_le_sqrt (lim v hv)).trans_eq (Real.sqrt_sq (by norm_num))) 
  · intro v hv
    rw [sq v hv]
    have eq := c.oscillation_energy_identity (slab hv) (turn v hv)
    dsimp only [D]
    field_simp [Real.pi_ne_zero] at *
    nlinarith only [eq]
  · intro e he v hv
    exact c.actual_directional_flux_bound (slab hv) (turn v hv) (small v hv) e he
  · intro e he
    have ht : t∈Icc s t := ⟨st,le_rfl⟩
    rw [sq t ht]
    exact c.actual_directional_support (slab ht) (turn t ht) (small t ht) e he

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.common_disk_on_low_bending_slab
