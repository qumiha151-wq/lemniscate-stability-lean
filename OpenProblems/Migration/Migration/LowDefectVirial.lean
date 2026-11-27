import Migration.LowDefectPhysicalDisk
import Migration.MaterialArclength
import Mathlib.Analysis.Fourier.AddCircle

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.LowDefect
theorem periodic_wirtinger {L : ℝ} (hL : 0<L) (f g : ℝ → ℂ) (hper : f L = f 0)
    (hf : ∀ s, HasDerivAt f (g s) s) (hg : Continuous g)
    (hmean : (∫ s in 0..L, f s) = 0) :
    (2*Real.pi)^2 * (∫ s in 0..L, ‖f s‖^2) ≤ L^2 * (∫ s in 0..L, ‖g s‖^2) := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun s => (hf s).continuousAt
  have lp (v : ℝ → ℂ) (hv : Continuous v) : MemLp v 2 (volume.restrict (Ioc 0 L)) := by
    apply (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mpr
    exact ((hv.norm.pow 2).intervalIntegrable 0 L).1
  have point (n : ℤ) : (2*Real.pi)^2 * ‖fourierCoeffOn hL f n‖^2 ≤
      L^2 * ‖fourierCoeffOn hL g n‖^2 := by
    by_cases hn : n=0
    · subst n
      have hz : fourierCoeffOn hL f 0 = 0 := by
        rw [fourierCoeffOn_eq_integral]; simp [hmean]
      rw [hz,norm_zero,zero_pow (by decide : 2≠0),mul_zero]
      positivity
    · have h := fourierCoeffOn_of_hasDerivAt hL hn (fun x _ => hf x) (hg.intervalIntegrable _ _)
      rw [hper,sub_self,mul_zero,zero_sub] at h
      have eqn := congrArg norm h
      simp only [norm_mul,norm_div,norm_one,norm_neg,Complex.norm_real,Real.norm_eq_abs,
        Complex.norm_I,mul_one,Complex.norm_intCast,abs_of_pos hL,abs_of_pos Real.pi_pos,
        Complex.ofReal_zero,sub_zero,Complex.norm_ofNat] at eqn
      have hnat : (1:ℝ) ≤ |(n:ℝ)| := by
        exact_mod_cast Int.one_le_abs hn
      have hprod : ‖fourierCoeffOn hL f n‖ * (2*Real.pi*|(n:ℝ)|) =
          L * ‖fourierCoeffOn hL g n‖ := by
        rw [eqn]
        field_simp [Real.pi_ne_zero, (by linarith : |(n:ℝ)| ≠ 0)]
      have hp : (2*Real.pi)*‖fourierCoeffOn hL f n‖ ≤ L*‖fourierCoeffOn hL g n‖ := by
        rw [← hprod]
        nlinarith only [mul_le_mul_of_nonneg_left hnat (show 0 ≤ (2*Real.pi)*‖fourierCoeffOn hL f n‖ by positivity)]
      simpa [mul_pow] using pow_le_pow_left₀ (by positivity) hp 2
  have bound := hasSum_le point
    ((hasSum_sq_fourierCoeffOn hL (lp f hc)).mul_left ((2*Real.pi)^2))
    ((hasSum_sq_fourierCoeffOn hL (lp g hg)).mul_left (L^2))
  simp only [sub_zero, smul_eq_mul] at bound
  apply (le_of_mul_le_mul_left (a:=L⁻¹) _ (inv_pos.mpr hL))
  linarith only [bound,show L⁻¹ * ((2*Real.pi)^2 * (∫ s in 0..L, ‖f s‖^2)) =
        (2*Real.pi)^2 * (L⁻¹ * (∫ s in 0..L, ‖f s‖^2)) by ring,
    show L⁻¹*(L^2*(∫ s in 0..L, ‖g s‖^2))=L^2*(L⁻¹*(∫ s in 0..L, ‖g s‖^2)) by ring]


end MigrationGeometry.Flow.LowDefect

namespace MigrationGeometry.Flow.PeriodicRegularPosition
variable (p : PeriodicRegularPosition)

theorem integral_complex_comp_inverse (f : ℝ → ℂ) (cf : Continuous f) :
    (∫ s in 0..p.length, f (p.arclengthInverse s)) =
      ∫ u in 0..p.period, speed p.position u • f u := by
  have h := intervalIntegral.integral_deriv_smul_comp
    (a:=0) (b:=p.period) (f:=p.arclength) (f':=speed p.position)
    (g:=fun s=>f (p.arclengthInverse s)) (fun u _=>p.arclength_hasDerivAt u)
    (speed_smooth p.smooth p.regular).continuous.continuousOn (cf.comp p.inverse_continuous)
  simpa only [Function.comp_apply,p.arclength_inverse_right,p.arclength_zero,
    p.arclength_length] using h.symm

theorem unit_position_hasDerivAt (s : ℝ) :
    HasDerivAt p.unitSpeedPosition (tangent p.position (p.arclengthInverse s)) s := by
  let u := p.arclengthInverse s
  have h := (position_hasDerivAt p.smooth p.regular (p.arclengthInverse s)).scomp s (p.inverse_hasDerivAt s)
  apply h.congr_deriv
  change (speed p.position u)⁻¹ • (speed p.position u • tangent p.position u) = _
  rw [smul_smul,inv_mul_cancel₀ (speed_pos p.regular u).ne',one_smul]

end MigrationGeometry.Flow.PeriodicRegularPosition
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

/-- The sharp periodic position moment follows from actual material data,
with no arclength parametrization or geometric radius bound as input. -/
theorem centered_position_wirtinger {t : ℝ} (ht : t ∈ I) :
    (2*Real.pi)^2 * (∫u in 0..c.period,
      ‖c.position t u-c.arclengthCentroid t‖^2*speed (c.position t) u) ≤
      (c.coreLength t)^3 := by
  let p : PeriodicRegularPosition := ⟨c.period,c.period_pos,c.position t,
    c.position_slice_smooth ht,c.periodic t ht,c.immersion t ht⟩
  let B := c.arclengthCentroid t
  let Y := fun u=>p.position u-B
  let f := fun s=>p.unitSpeedPosition s-B
  let g := fun s=>tangent p.position (p.arclengthInverse s)
  have l : p.length=c.coreLength t := rfl
  have cy : Continuous Y := p.smooth.continuous.sub continuous_const
  have per : f p.length=f 0 := by
    simp only [f,PeriodicRegularPosition.unitSpeedPosition,p.inverse_length,p.inverse_zero]
    have h := p.periodic 0
    rw [zero_add] at h
    rw [h]
  have dg (s : ℝ) : HasDerivAt f (g s) s := (p.unit_position_hasDerivAt s).sub_const _
  have cg : Continuous g := (tangent_smooth p.smooth p.regular).continuous.comp p.inverse_continuous
  have mass : (∫s in 0..p.length,f s)=0 := by
    change (∫s in 0..p.length,Y (p.arclengthInverse s))=0
    rw [p.integral_complex_comp_inverse Y cy]
    change (∫u in 0..p.period,speed p.position u • (p.position u-B))=0
    simp only [smul_sub]
    have csp := (speed_smooth p.smooth p.regular).continuous
    rw [intervalIntegral.integral_sub (f:=fun u=>speed p.position u • p.position u)
      (g:=fun u=>speed p.position u • B) ((csp.smul p.smooth.continuous).intervalIntegrable ..)
      ((csp.smul (continuous_const (y:=B))).intervalIntegrable ..),intervalIntegral.integral_smul_const]
    change (∫u in 0..c.period,speed (c.position t) u • c.position t u) -
      c.coreLength t • ((c.coreLength t)⁻¹ • (∫u in 0..c.period,speed (c.position t) u • c.position t u))=0
    rw [smul_smul,mul_inv_cancel₀ (c.coreLength_pos ht).ne',one_smul,sub_self]
  have wr := LowDefect.periodic_wirtinger p.length_pos f g per dg cg mass
  have prod : (∫s in 0..p.length,‖f s‖^2)=∫u in 0..p.period,‖Y u‖^2*speed p.position u :=
    p.integral_comp_inverse (f:=fun u=>‖Y u‖^2) (cy.norm.pow 2)
  have unit (s : ℝ) : ‖g s‖=1 := tangent_unit p.regular _
  rw [prod] at wr
  simp only [unit,one_pow,intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one,l] at wr
  change (2*Real.pi)^2*(∫u in 0..p.period,‖Y u‖^2*speed p.position u) ≤ (c.coreLength t)^3
  linarith only [wr,show (c.coreLength t)^2*c.coreLength t=(c.coreLength t)^3 by ring]

theorem centered_support_wirtinger {t : ℝ} (ht : t ∈ I) :
    (2*Real.pi)^2*c.centeredSupportMoment t ≤ (c.coreLength t)^3 := by
  apply le_trans _ (c.centered_position_wirtinger ht)
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have hγ := c.position_slice_smooth ht
  have hreg := c.immersion t ht
  have cY := hγ.continuous.sub (continuous_const (y:=c.arclengthCentroid t))
  have cg := (speed_smooth hγ hreg).continuous
  apply intervalIntegral.integral_mono_on c.period_pos.le
    (((((normal_smooth hγ hreg).continuous.inner cY).pow 2).mul cg).intervalIntegrable ..)
    (((cY.norm.pow 2).mul cg).intervalIntegrable ..)
  intro u _
  apply mul_le_mul_of_nonneg_right _ (speed_pos hreg u).le
  have h := abs_real_inner_le_norm (normal (c.position t) u) (c.position t u-c.arclengthCentroid t)
  rw [normal_unit hreg,one_mul] at h
  simpa using pow_le_pow_left₀ (abs_nonneg _) h 2

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.centered_support_wirtinger
