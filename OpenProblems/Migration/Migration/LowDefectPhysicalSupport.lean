import Migration.LowDefectMaterialSupport
import Migration.LowDefectDiskComparison

noncomputable section
open Set MeasureTheory
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem actual_directional_support {t : ℝ} (ht : t∈I)
    (turn : c.signedCurvatureIntegral t=2*Real.pi)
    (small : c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2≤14/100)
    (e : ℂ) (he : ‖e‖=1) :
    let D := c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2
    ∃u∈Icc 0 c.period, inner ℝ e (c.arclengthCentroid t)+
      c.coreLength t/(2*Real.pi)*(1-575/1000*Real.sqrt D-265/1000*D) ≤ inner ℝ e (c.position t u) := by
  let p := c.materialSlice ht
  let D := c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2
  obtain ⟨x,hx,val⟩ := (c.material_normalized_support ht turn small).2 e he
  let u := p.arclengthInverse (p.length*x)
  have ord : Monotone p.arclengthInverse := p.arclengthOrderIso.symm.monotone
  have ll : 0≤u := by
    rw [←p.inverse_zero]; exact ord (mul_nonneg p.length_pos.le hx.1)
  have rr : u≤p.period := by
    rw [←p.inverse_length]; exact ord (by simpa using mul_le_mul_of_nonneg_left hx.2.le p.length_pos.le)
  refine ⟨u,⟨ll,rr⟩,?_⟩
  change 1-132/1000*D-(575/1000*Real.sqrt D+133/1000*D) ≤
    inner ℝ e ((2*Real.pi/p.length) • (p.position u-c.arclengthCentroid t)) at val
  rw [real_inner_smul_right,inner_sub_right] at val
  have a : 0<2*Real.pi := by positivity
  have pos : 0≤p.length/(2*Real.pi) := div_nonneg p.length_pos.le a.le
  have h := mul_le_mul_of_nonneg_left val pos
  rw [←mul_assoc,div_mul_div_cancel₀ a.ne',div_self p.length_pos.ne',one_mul] at h
  change inner ℝ e (c.arclengthCentroid t)+p.length/(2*Real.pi)*(1-575/1000*Real.sqrt D-265/1000*D) ≤ inner ℝ e (p.position u)
  linarith only [h]

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.actual_directional_support
