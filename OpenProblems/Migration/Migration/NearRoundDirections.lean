import Migration.NearRoundSupport
import Mathlib.Analysis.Calculus.LocalExtr.Basic

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

/-- The range of the normal needed at the directional maximum comes from
the actual regular curve and the scalar curvature oscillation itself. -/
theorem near_round_hits_negative_normal {t S a : ℝ} (ht : t ∈ I) (hS : 0 < S)
    (ha : 0 ≤ a) (ha1 : a < 1) (ho : c.curvatureOscillation S t ≤ a^2)
    (e : ℂ) (he : ‖e‖ = 1) :
    ∃ u ∈ Icc 0 c.period, inner ℝ e (normal (c.position t) u) = -1 := by
  let H : ℂ →L[ℝ] ℝ := innerSL ℝ e
  let γ := c.position t
  let h := fun u => H (γ u)
  have hH : ‖H‖ ≤ 1 := by dsimp [H]; rw [innerSL_apply_norm, he]
  have hg := c.position_slice_smooth ht
  have hr := c.immersion t ht
  have hc : Continuous h := H.continuous.comp hg.continuous
  have hper : Function.Periodic h c.period := fun u => by dsimp [h,γ]; rw [c.periodic t ht u]
  obtain ⟨v,hv,hmax⟩ := isCompact_Icc.exists_isMaxOn (show (Icc 0 c.period).Nonempty from
    ⟨0,le_rfl,c.period_pos.le⟩) hc.continuousOn
  have hglobal (u : ℝ) : h u ≤ h v := by
    obtain ⟨w,hw,hw'⟩ := hper.exists_mem_Ico₀ c.period_pos u
    rw [hw']
    exact hmax ⟨hw.1,hw.2.le⟩
  have hm : IsLocalMax h v := Filter.Eventually.of_forall hglobal
  have hd : HasDerivAt h (speed γ v * H (tangent γ v)) v := by
    apply (H.hasFDerivAt.comp_hasDerivAt v (position_hasDerivAt hg hr v)).congr_deriv
    rw [map_smul, smul_eq_mul]
  have hT : H (tangent γ v) = 0 :=
    (mul_eq_zero.mp (hm.hasDerivAt_eq_zero hd)).resolve_left (speed_pos hr v).ne'
  have hb : c.centroidHeight H t ≤ h v := by
    apply (div_le_iff₀ (c.coreLength_pos ht)).mpr
    have cs := (speed_smooth hg hr).continuous
    have hi := intervalIntegral.integral_mono_on (μ := volume) c.period_pos.le
      ((hc.mul cs).intervalIntegrable _ _) ((cs.const_mul (h v)).intervalIntegrable _ _)
      (fun u _ => mul_le_mul_of_nonneg_right (hglobal u) (speed_pos hr u).le)
    change (∫ u in 0..c.period, h u * speed γ u) ≤ ∫ u in 0..c.period, h v * speed γ u at hi
    rwa [intervalIntegral.integral_const_mul] at hi
  have hframe (z : ℂ) :
      (inner ℝ e z)^2+(inner ℝ e (Complex.I*z))^2 = ‖e‖^2*‖z‖^2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.inner, Complex.inner]
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.I_re, Complex.I_im]
    ring
  have hsq := hframe (tangent γ v)
  change inner ℝ e (tangent γ v) = 0 at hT
  rw [hT, he, tangent_unit hr] at hsq
  change (0:ℝ)^2+(H (normal γ v))^2=1^2*1^2 at hsq
  have hn : H (normal γ v) = -1 ∨ H (normal γ v) = 1 := by
    exact (mul_eq_zero.mp (show (H (normal γ v)+1)*(H (normal γ v)-1)=0 by nlinarith)).imp
      (fun h => by linarith) sub_eq_zero.mp
  refine ⟨v,hv,hn.resolve_right ?_⟩
  intro hbad
  have hdef := (abs_le.mp (c.height_normal_defect H hH ht hS ha ho hv)).2
  change (h v-c.centroidHeight H t)/c.coreLength t+H (normal γ v)/S ≤ a/S at hdef
  rw [hbad] at hdef
  have hpos := div_nonneg (sub_nonneg.mpr hb) (c.coreLength_pos ht).le
  linarith [div_lt_div_of_pos_right ha1 hS]

#print axioms near_round_hits_negative_normal
end MigrationGeometry.Flow.SmoothPeriodicImmersion
