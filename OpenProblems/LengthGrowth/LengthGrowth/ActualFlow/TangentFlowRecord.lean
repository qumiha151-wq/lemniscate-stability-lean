import LengthGrowth.ActualFlow.TangentFrenetSpectrum
import LengthGrowth.ActualFlow.CriticalRMSAdapter
import LengthGrowth.ActualFlow.MacroscopicTurningRecords
import LengthGrowth.ActualFlow.EventualCurvatureSign
namespace LengthGrowth.ActualFlow.ForwardImmersion
noncomputable section
open Real Set MeasureTheory Filter TangentSpectrum
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable (c : ForwardImmersion)

theorem signed_fourier_at_record (hf : c.IsNormalFEF) {t X : ℝ} (ht : 0<t) (xp : 0<X)
    (scale : X^3=c.normalizedProduct t)
    (record : ∀s∈Icc 0 t,c.normalizedProduct s≤c.normalizedProduct t) :
    let T := (c.regularPositionAt ht.le).closedFrenetCurve.unitT
    HasSum (fun n : ℤ=>omega n*TangentSpectrum.energy T n) (materialSignedCurvature (c.position 0) c.period) ∧
    HasSum (fun n : ℤ=>|omega n|^2*TangentSpectrum.energy T n) (2*X^3) ∧
    ∃M, HasSum (fun n : ℤ=>|omega n|^4*TangentSpectrum.energy T n) M ∧ M≤1024*X^7 := by
  let p:=c.regularPositionAt ht.le
  let a:=p.closedFrenetCurve
  let L:=c.length t
  let E:=c.energy t
  let D:=c.dissipation t
  have lp : 0<L:=c.length_pos ht.le
  have ep : 0<E:=c.energy_pos ht.le
  have dn : 0≤D:=c.dissipation_nonneg _
  have xs : X^3=E*L:=scale
  have hd:=c.dissipation_at_product_record hf ht record
  change 4*(D*L^2/(8*E^3))≤1 at hd
  have hb : D*L^2≤2*E^3 := by
    have he8 : 0<(8:ℝ)*E^3 := by positivity
    rw [mul_div_assoc',div_le_iff₀ he8] at hd
    linarith only [hd]
  have slopes := (hasDerivAt_iff_tendsto_slope_left_right.mp (c.normalizedProduct_hasDerivAt_normal hf ht)).1
  have rate : 0≤E*c.lengthRate t-L*D := by
    apply ge_of_tendsto slopes
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Ioi_mem_nhds ht)] with x hx hxp
    rw [slope_def_field]
    exact div_nonneg_of_nonpos (sub_nonpos.mpr (record x ⟨hxp.le,hx.le⟩)) (sub_nonpos.mpr hx.le)
  have rn : 0≤c.lengthRate t := nonneg_of_mul_nonneg_right ((mul_nonneg lp.le dn).trans (sub_nonneg.mp rate)) ep
  have force' : (fun s=>deriv (deriv (p.scaledArclengthCurvature L)) s+1/2*(p.scaledArclengthCurvature L s)^3)=
      fun s=>a.unitC s+a.unitK s^3/2 := by
    have der1 : deriv (p.scaledArclengthCurvature L)=a.unitB := funext fun u=>(a.unitK_der u).deriv
    have der2 : deriv a.unitB=a.unitC := funext fun u=>(a.unitB_der u).deriv
    funext u;rw [der1,der2];change _+1/2*(a.unitK u)^3=_;ring
  have moments:=p.scaledArclengthCurvature_moment lp (by norm_num : (0:ℝ)<1) (show L*1=p.length by rw [mul_one];rfl)
  have m1:=moments 1 0
  have m2:=moments 2 0
  have dv:=moments 1 1
  simp only [pow_zero,pow_one,mul_one,div_one] at m1 m2 dv
  change (∫u in 0..1,a.unitK u)=L/L*materialSignedCurvature (c.position t) c.period at m1
  rw [div_self lp.ne',one_mul,c.signedCurvature_eq_initial ht.le] at m1
  change (∫u in 0..1,a.unitK u^2)=L^2/L*(∫s in 0..p.period,curvature p.position s^2*speed p.position s) at m2
  have en : (∫s in 0..p.period,curvature p.position s^2*speed p.position s)=2*E := by
    change _=2*(1/2*(∫s in 0..p.period,curvature p.position s^2*speed p.position s));ring
  have mass : (∫u in 0..1,a.unitK u^2)=2*X^3 := by rw [m2,en,xs];field_simp [lp.ne']
  change (∫u in 0..1,a.unitK u*((fun s=>deriv (deriv (p.scaledArclengthCurvature L)) s+1/2*(p.scaledArclengthCurvature L s)^3) u))=L*L^3/L*c.lengthRate t at dv
  rw [force'] at dv
  have work : 0≤∫u in 0..1,a.unitK u*(a.unitC u+a.unitK u^3/2) := dv.symm ▸ mul_nonneg (by positivity) rn
  have stress (u : ℝ) : |a.unitK u|^6≤(2^25:ℝ)*X^12 := by
    have raw:=a.energy_dissipation_controls_curvature (L*u)
    have ae : a.energy=E:=p.closedFrenetCurve_energy
    have ad : a.dissipation=D:=p.closedFrenetCurve_dissipation
    rw [ae,ad] at raw
    change |L*a.curvature (L*u)|^6≤_
    rw [abs_mul,abs_of_pos lp,mul_pow,show X^12=(X^3)^4 by ring,xs]
    have wraw:=mul_le_mul_of_nonneg_left raw (show 0≤(16777216:ℝ)*L^6 by positivity)
    have wbound:=mul_le_mul_of_nonneg_left hb (show 0≤(16777216:ℝ)*E*L^4 by positivity)
    nlinarith only [wraw,wbound]
  have result:=a.unitT_spectral X xp mass stress work
  rwa [m1] at result
end
end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.signed_fourier_at_record
