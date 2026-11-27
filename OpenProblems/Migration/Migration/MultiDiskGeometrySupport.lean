import Migration.MultiDiskGeometrySupportCore
import Migration.MultiDiskPointwise

noncomputable section
open Set MeasureTheory
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

/-- A pointwise position-normal error in terms of the measured curvature
oscillation, valid at every fractional arclength label. -/
theorem multi_correction_bound {t : ℝ} (ht : t∈I) (m s : ℝ) :
    ‖(c.materialSlice ht).coverCorrection m (c.arclengthCentroid t) s‖≤
      (91/50)*(Real.sqrt (c.curvatureOscillation (2*Real.pi*m) t)/(2*Real.pi)) := by
  let p := c.materialSlice ht
  let B := c.arclengthCentroid t
  let V := c.curvatureOscillation (2*Real.pi*m) t
  have v : 0≤V := c.curvatureOscillation_nonneg ht _
  have pos : 0<2*Real.pi := by positivity
  apply MultiDisk.unit_period_scaled_point_bound (div_nonneg (Real.sqrt_nonneg _) pos.le)
    (p.coverCorrection_periodic m B) (p.coverRate_periodic m)
    (p.coverCorrection_derivative m B) (p.coverRate_continuous m) (c.multi_correction_mean ht m) _ s
  have cancel : (2*Real.pi)*(Real.sqrt V/(2*Real.pi))=Real.sqrt V := by field_simp
  rw [c.multi_rate_moment ht m]
  change V≤(2*Real.pi*(Real.sqrt V/(2*Real.pi)))^2
  rw [cancel,Real.sq_sqrt v]

theorem multi_position_bound {t : ℝ} (ht : t∈I) (m : ℝ) :
    ∀s∈Icc (0:ℝ) 1, ‖(c.materialSlice ht).coverPosition m (c.arclengthCentroid t) s‖≤
      1+(91/50)*(Real.sqrt (c.curvatureOscillation (2*Real.pi*m) t)/(2*Real.pi)) :=
  fun s _=>(c.materialSlice ht).coverPosition_bound_of_correction (c.multi_correction_bound ht m) s

/-- Every unit direction has the stated physical support above the
arclength centroid of the material time slice. -/
theorem multi_directional_support {t m : ℝ} (ht : t∈I) (hm : 0<m)
    (small : Real.sqrt (c.curvatureOscillation (2*Real.pi*m) t)/(2*Real.pi)≤1/4)
    (e : ℂ) (he : ‖e‖=1) :
    ∃u∈Icc 0 c.period, inner ℝ e (c.arclengthCentroid t)+
      (c.coreLength t/(2*Real.pi*m))*(1-(91/50)*(Real.sqrt (c.curvatureOscillation (2*Real.pi*m) t)/(2*Real.pi)))
      ≤ inner ℝ e (c.position t u) :=
  c.multi_support_of_correction ht hm (by linarith) (c.multi_correction_bound ht m) e he

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.multi_directional_support
