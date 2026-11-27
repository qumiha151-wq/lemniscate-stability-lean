import Migration.MultiDiskGeometry
import Migration.ProjectedHeightTransit

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.PeriodicRegularPosition
variable (p : PeriodicRegularPosition)

theorem coverRate_periodic (m : ℝ) : Function.Periodic (p.coverRate m) 1 := by
  intro s
  simp only [coverRate,fractionalCurvature,fractionalTangent,mul_add,mul_one,p.inverse_add_length,
    curvature_periodic p.smooth p.regular p.periodic _,tangent_periodic p.smooth p.periodic _]

theorem coverPosition_bound_of_correction {m D : ℝ} {B : ℂ}
    (bound : ∀s, ‖p.coverCorrection m B s‖≤D) (s : ℝ) :
    ‖p.coverPosition m B s‖≤1+D := by
  have unit : ‖Complex.I*p.fractionalTangent s‖=1 := by
    rw [norm_mul,Complex.norm_I,show ‖p.fractionalTangent s‖=1 from tangent_unit p.regular _,one_mul]
  have triangle := norm_sub_le (p.coverCorrection m B s) (Complex.I*p.fractionalTangent s)
  rw [coverCorrection,add_sub_cancel_right,unit] at triangle
  change ‖p.coverPosition m B s‖≤‖p.coverCorrection m B s‖+1 at triangle
  linarith [bound s]

end MigrationGeometry.Flow.PeriodicRegularPosition
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

/-- The support direction is attained by the actual material slice. At a
height maximum the two possible normal signs are distinguished by the
centered position and the uniform correction bound. -/
theorem multi_support_of_correction {t m D : ℝ} (ht : t∈I) (hm : 0<m) (small : D<1)
    (bound : ∀s, ‖(c.materialSlice ht).coverCorrection m (c.arclengthCentroid t) s‖≤D)
    (e : ℂ) (he : ‖e‖=1) :
    ∃u∈Icc 0 c.period, inner ℝ e (c.arclengthCentroid t)+
      (c.coreLength t/(2*Real.pi*m))*(1-D) ≤ inner ℝ e (c.position t u) := by
  let p := c.materialSlice ht
  let B := c.arclengthCentroid t
  let H : ℂ →L[ℝ] ℝ := innerSL ℝ e
  let h := fun u=>H (p.position u)
  have ch : Continuous h := H.continuous.comp p.smooth.continuous
  have per : Function.Periodic h p.period := fun u=> by dsimp only [h];rw [p.periodic u]
  obtain ⟨v,hv,maximal⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc 0 p.period).Nonempty from ⟨0,le_rfl,p.period_pos.le⟩) ch.continuousOn
  have top (u : ℝ) : h u≤h v := by
    obtain ⟨w,hw,hw'⟩ := per.exists_mem_Ico₀ p.period_pos u
    rw [hw'];exact maximal ⟨hw.1,hw.2.le⟩
  have extreme : IsLocalMax h v := Filter.Eventually.of_forall top
  have derivative : HasDerivAt h (speed p.position v*H (tangent p.position v)) v := by
    apply (H.hasFDerivAt.comp_hasDerivAt v (position_hasDerivAt p.smooth p.regular v)).congr_deriv
    rw [map_smul,smul_eq_mul]
  have htang : H (tangent p.position v)=0 :=
    (mul_eq_zero.mp (extreme.hasDerivAt_eq_zero derivative)).resolve_left (speed_pos p.regular v).ne'
  have hnormal := unit_projection_identity he (tangent p.position v)
  change (H (tangent p.position v))^2+(H (normal p.position v))^2=‖tangent p.position v‖^2 at hnormal
  rw [htang,tangent_unit p.regular] at hnormal
  have signs : H (normal p.position v) = -1 ∨ H (normal p.position v)=1 := by
    exact (mul_eq_zero.mp (show (H (normal p.position v)+1)*(H (normal p.position v)-1)=0 by nlinarith)).imp
      (fun h=>by linarith) sub_eq_zero.mp
  have hb : H B≤h v := by
    rw [show H B=c.centroidHeight H t from c.map_arclengthCentroid H ht]
    apply (div_le_iff₀ (c.coreLength_pos ht)).mpr
    have cs := (speed_smooth p.smooth p.regular).continuous
    have z := intervalIntegral.integral_mono_on (μ:=volume) p.period_pos.le
      ((ch.mul cs).intervalIntegrable ..) ((cs.const_mul (h v)).intervalIntegrable ..)
      (fun u _=>mul_le_mul_of_nonneg_right (top u) (speed_pos p.regular u).le)
    change (∫u in 0..p.period,h u*speed p.position u)≤∫u in 0..p.period,h v*speed p.position u at z
    rwa [intervalIntegral.integral_const_mul] at z
  let s := p.arclength v/p.length
  have label : p.arclengthInverse (p.length*s)=v := by
    rw [show p.length*s=p.arclength v by dsimp only [s];field_simp [p.length_pos.ne'],p.arclength_inverse_right]
  have innerbound : |H (p.coverCorrection m B s)|≤D :=
    (abs_real_inner_le_norm e (p.coverCorrection m B s)).trans (by simpa only [he,one_mul] using bound s)
  change |H (m • ((2*Real.pi/p.length) •
    (p.position (p.arclengthInverse (p.length*s))-B))+normal p.position (p.arclengthInverse (p.length*s)))|≤D at innerbound
  rw [label,map_add,map_smul,map_smul,map_sub] at innerbound
  change |m*((2*Real.pi/p.length)*(h v-H B))+H (normal p.position v)|≤D at innerbound
  have pos : 0 < 2*Real.pi*m := by positivity
  have diff : 0≤m*((2*Real.pi/p.length)*(h v-H B)) :=
    mul_nonneg hm.le (mul_nonneg (div_nonneg (by positivity) p.length_pos.le) (sub_nonneg.mpr hb))
  have minus := signs.resolve_right (fun plus=>by rw [plus] at innerbound; linarith [(abs_le.mp innerbound).2])
  rw [minus] at innerbound
  have lower : 1-D≤m*((2*Real.pi/p.length)*(h v-H B)) := by linarith [(abs_le.mp innerbound).1]
  have mult := mul_le_mul_of_nonneg_left lower (div_nonneg p.length_pos.le pos.le)
  have ident : (p.length/(2*Real.pi*m))*(m*((2*Real.pi/p.length)*(h v-H B)))=h v-H B := by
    field_simp [Real.pi_ne_zero,hm.ne',p.length_pos.ne']
  rw [ident] at mult
  exact ⟨v,hv,by change H B+p.length/(2*Real.pi*m)*(1-D)≤h v; linarith⟩

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.multi_support_of_correction
