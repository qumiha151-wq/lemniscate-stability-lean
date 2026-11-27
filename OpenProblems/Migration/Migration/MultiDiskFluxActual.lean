import Migration.MultiDiskFluxSlab
import Migration.MultiDiskGeometrySupport
import Migration.SublevelPhysicalDisk

noncomputable section
open Set MeasureTheory
open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem multi_disk_on_bending_slab (hf : c.IsNormalFEF) {m s t : ℝ} (hm : 2≤m)
    (st : s≤t) (slab : Icc s t⊆I) (turn : ∀v∈Icc s t,c.signedCurvatureIntegral v=2*Real.pi*m)
    (energy : ∀v∈Icc s t,2*c.bending v*c.coreLength v≤(2*Real.pi*m)^2+Real.pi^2/4) :
    Metric.closedBall (c.arclengthCentroid s)
      ((1+(1/m)^2/16)*((54/100)*(Real.pi*m)/c.bending s+(1/200)*(Real.pi*m)/c.bending t)) ⊆
        convexHull ℝ (c.position t '' Icc 0 c.period) := by
  let d:=fun r=>c.curvatureOscillation (2*Real.pi*m) r
  let x:=fun r=>Real.sqrt (d r)/(2*Real.pi)
  have mp : 0<m := by linarith
  have pp : 0<2*Real.pi := by positivity
  have dp r (hr : r∈Icc s t) : 0≤d r:=c.curvatureOscillation_nonneg (slab hr) _
  have hx r : 0≤x r := div_nonneg (Real.sqrt_nonneg _) pp.le
  have xeq r (hr : r∈Icc s t) : d r=(2*Real.pi)^2*(x r)^2 := by
    dsimp only [x];rw [div_pow,Real.sq_sqrt (dp r hr)];field_simp
  have top r (hr : r∈Icc s t) : x r≤1/4 := by
    have ee:=c.oscillation_energy_identity (slab hr) (turn r hr)
    have b:=energy r hr
    change _=(2*Real.pi*m)^2+d r at ee
    change Real.sqrt (d r)/(2*Real.pi)≤1/4
    apply (div_le_iff₀ pp).mpr
    apply (Real.sqrt_le_iff).mpr ⟨by positivity,?_⟩
    nlinarith only [b,ee]
  apply c.multi_disk_of_snapshot_moments hf hm st slab x (fun r _=>hx r) top
  · intro r hr
    have eq:=c.oscillation_energy_identity (slab hr) (turn r hr)
    change _=(2*Real.pi*m)^2+d r at eq
    rw [xeq r hr] at eq
    field_simp [mp.ne'];nlinarith only [eq]
  · intro e he r hr
    have M:=c.multi_correction_moment (slab hr) m
    change _≤d r at M
    rw [xeq r hr] at M
    exact c.multi_material_flux_moments (slab hr) mp (hx r) (xeq r hr)
      ((mul_le_mul_iff_right₀ (sq_pos_of_pos pp)).mp M) (c.multi_position_bound (slab hr) m) e he
  · exact c.multi_directional_support (slab ⟨st,le_rfl⟩) mp (top t ⟨st,le_rfl⟩)

theorem multi_disk_on_abs_bending_slab (hf : c.IsNormalFEF) {m s t : ℝ} (hm : 2≤m)
    (st : s≤t) (slab : Icc s t⊆I) (turn : ∀v∈Icc s t,|c.signedCurvatureIntegral v|=2*Real.pi*m)
    (energy : ∀v∈Icc s t,2*c.bending v*c.coreLength v≤(2*Real.pi*m)^2+Real.pi^2/4) :
    Metric.closedBall (c.arclengthCentroid s)
      ((1+(1/m)^2/16)*((54/100)*(Real.pi*m)/c.bending s+(1/200)*(Real.pi*m)/c.bending t)) ⊆
        convexHull ℝ (c.position t '' Icc 0 c.period) := by
  have mp : 0<m := by linarith
  have A : 0<2*Real.pi*m := by positivity
  have hs : s∈Icc s t:=⟨le_rfl,st⟩
  have ht : t∈Icc s t:=⟨st,le_rfl⟩
  have sign (f : SmoothPeriodicImmersion I) (positive : 0≤f.signedCurvatureIntegral s)
      (T : ∀v∈Icc s t,|f.signedCurvatureIntegral v|=2*Real.pi*m) :
      ∀v∈Icc s t,f.signedCurvatureIntegral v=2*Real.pi*m := by
    intro v hv
    by_cases pos : 0≤f.signedCurvatureIntegral v
    · simpa [abs_of_nonneg pos] using T v hv
    have sub : Icc s v⊆Icc s t:=Icc_subset_Icc_right hv.2
    obtain ⟨y,hy,zero⟩:=intermediate_value_Icc' hv.1 ((f.scalar_turn_continuous_slab slab).mono sub)
      (show 0∈Icc (f.signedCurvatureIntegral v) (f.signedCurvatureIntegral s) from ⟨(lt_of_not_ge pos).le,positive⟩)
    have H:=T y (sub hy)
    rw [zero,abs_zero] at H
    linarith
  by_cases plus : 0≤c.signedCurvatureIntegral s
  · exact c.multi_disk_on_bending_slab hf hm st slab (sign c plus turn) energy
  have pos : 0≤c.reflected.signedCurvatureIntegral s := by rw [c.reflected_turn (slab hs)];linarith
  have reflection:=c.reflected.multi_disk_on_bending_slab (c.reflected_flow hf) hm st slab
    (sign c.reflected pos (fun r hr=>by rw [c.reflected_turn (slab hr),abs_neg];exact turn r hr))
    (fun r hr=>by rw [c.reflected_bending (slab hr),c.reflected_length (slab hr)];exact energy r hr)
  rw [c.reflected_centroid (slab hs),c.reflected_bending (slab hs),c.reflected_bending (slab ht)] at reflection
  intro z hz
  have eq:=Complex.conjLIE.isometry.dist_eq z (c.arclengthCentroid s)
  have zz:=reflection (show conj z∈_ from Metric.mem_closedBall.mpr (eq.trans_le (Metric.mem_closedBall.mp hz)))
  let F : ℂ→ₗ[ℝ] ℂ:=Complex.conjCLE.toLinearEquiv.toLinearMap
  have image_eq : c.reflected.position t '' Icc 0 c.period=F '' (c.position t '' Icc 0 c.period) := by rw [Set.image_image];rfl
  change conj z∈convexHull ℝ (c.reflected.position t '' Icc 0 c.period) at zz
  rw [image_eq,←F.image_convexHull] at zz
  obtain ⟨v,hv,h⟩:=zz
  exact Complex.conjCLE.injective h ▸ hv

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.multi_disk_on_abs_bending_slab

