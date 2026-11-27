import LengthGrowth.ActualFlow.PhysicalSaturationGap
import LengthGrowth.ActualFlow.GrowthEquivalence

noncomputable section
open MeasureTheory Set
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

/-- Smooth density tending to twice the arclength-curvature slope mass at the zeros. -/
def nodalSlopeDensity (b s : ℝ) :=
  b^2*c.curvature₁ s^2/(Real.sqrt (c.curvature s^2+b^2))^3

def nodalSlopeMass (b : ℝ) := ∫s in 0..c.period, c.nodalSlopeDensity b s

theorem energy_rms_le_nodal_force {b m : ℝ} (hb : 0<b) (hm : 0≤m)
    (rms : m^2*c.period=2*c.energy) :
    c.energy*m ≤ c.nodalSlopeMass b+b*c.energy+Real.sqrt (c.period*c.dissipation) := by
  let q := fun s=>Real.sqrt (c.curvature s^2+b^2)
  let u := fun s=>c.curvature s/q s
  have ck := c.curvature_continuous
  have cp := c.curvature₁_continuous
  have cq : Continuous q := ((ck.pow 2).add continuous_const).sqrt
  have qp (s : ℝ) : 0<q s := Real.sqrt_pos.mpr (by positivity)
  have q2 (s : ℝ) : q s^2=c.curvature s^2+b^2 := Real.sq_sqrt (by positivity)
  have cu : Continuous u := ck.div cq (fun s=>(qp s).ne')
  have cd : Continuous (c.nodalSlopeDensity b) := ((cp.pow 2).const_mul _).div
    (cq.pow 3) (fun s=>pow_ne_zero _ (qp s).ne')
  have dq (s : ℝ) : HasDerivAt q (c.curvature s*c.curvature₁ s/q s) s := by
    apply ((((c.curvature_deriv s).pow 2).add_const (b^2)).sqrt
      (show c.curvature s^2+b^2 ≠ 0 by positivity)).congr_deriv
    dsimp [q]; ring
  have du (s : ℝ) : HasDerivAt u (b^2*c.curvature₁ s/q s^3) s := by
    apply ((c.curvature_deriv s).div (dq s) (qp s).ne').congr_deriv
    dsimp only [q,u] at *
    field_simp [(qp s).ne']
    nlinarith only [congrArg (fun z:ℝ=>c.curvature₁ s*z) (q2 s)]
  let v := fun s=>c.curvature s^4/(2*q s)
  have cv : Continuous v := (ck.pow 4).div (continuous_const.mul cq) (fun s=>mul_ne_zero (by norm_num) (qp s).ne')
  have cf := cu.mul c.force_continuous
  have hd (s : ℝ) : HasDerivAt (fun z=>u z*c.curvature₁ z)
      ((c.nodalSlopeDensity b s+u s*c.force s)-v s) s := by
    apply ((du s).mul (c.curvature₁_deriv s)).congr_deriv
    change b^2*c.curvature₁ s/q s^3*c.curvature₁ s + u s*c.curvature₂ s = _
    change _ = (b^2*c.curvature₁ s^2/q s^3+u s*(c.curvature₂ s+c.curvature s^3/2))-c.curvature s^4/(2*q s)
    dsimp only [u]; ring
  have ft := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=c.period) (fun s _=>hd s)
    (((cd.add cf).sub cv).intervalIntegrable ..)
  have kp : c.curvature c.period=c.curvature 0 := by simpa using c.curvature_periodic 0
  have perp : c.curvature₁ c.period=c.curvature₁ 0 := by simpa using c.curvature₁_periodic 0
  have per : u c.period=u 0 := by simp [u,q,kp]
  rw [per,perp,sub_self,intervalIntegral.integral_sub (f:=fun s=>c.nodalSlopeDensity b s+u s*c.force s)
    (g:=v) ((cd.add cf).intervalIntegrable ..) (cv.intervalIntegrable ..),
    intervalIntegral.integral_add (f:=c.nodalSlopeDensity b) (g:=fun s=>u s*c.force s)
      (cd.intervalIntegrable ..) (cf.intervalIntegrable ..)] at ft
  have absle (s : ℝ) : |c.curvature s|≤q s := by
    apply le_of_sq_le_sq _ (qp s).le
    rw [sq_abs,q2]; linarith [sq_nonneg b]
  have bq (s : ℝ) : b≤q s := by
    apply le_of_sq_le_sq _ (qp s).le
    rw [q2]; linarith [sq_nonneg (c.curvature s)]
  have hforce := intervalIntegral.integral_mono_on (μ:=volume) c.period_pos.le (cf.intervalIntegrable ..)
    (c.force_continuous.abs.intervalIntegrable ..) (fun s _ => calc
    u s*c.force s ≤ |u s*c.force s| := le_abs_self _
    _ ≤ |c.force s| := by
      rw [abs_mul]; apply mul_le_of_le_one_left (abs_nonneg _)
      rw [show u s=c.curvature s/q s by rfl,abs_div,abs_of_pos (qp s), div_le_one (qp s)]
      exact absle s)
  have cs := LengthGrowth.interval_integral_mul_sq_le c.force_continuous.abs
    (continuous_const (y:=(1:ℝ))) c.period_pos.le
  simp only [mul_one, sq_abs, one_pow, intervalIntegral.integral_const,sub_zero,smul_eq_mul] at cs
  have upper : (∫s in 0..c.period,u s*c.force s)≤Real.sqrt (c.period*c.dissipation) := by
    apply hforce.trans
    apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt (mul_nonneg c.period_pos.le c.dissipation_nonneg),mul_comm]
    exact cs
  let A := 3*m/4-b/2
  have point (s : ℝ) : A*c.curvature s^2-m^3/4 ≤ v s := by
    let z := |c.curvature s|
    have z2 : z^2=c.curvature s^2 := sq_abs _
    have zq : z≤q s := absle s
    have approx : z-b≤c.curvature s^2/q s := by
      apply (le_div_iff₀ (qp s)).mpr
      have raw := mul_le_mul_of_nonneg_right zq (qp s).le
      have raw2 := mul_le_mul_of_nonneg_left (bq s) hb.le
      nlinarith only [raw,raw2,q2 s]
    have pos := mul_nonneg (sq_nonneg (z-m)) (show 0≤z+m/2 by positivity)
    have est := mul_le_mul_of_nonneg_right approx (sq_nonneg z)
    rw [← z2] at est
    dsimp only [A,v]
    rw [show c.curvature s^4=(z^2)^2 by rw [z2];ring,←z2]
    rw [show (z^2)^2/(2*q s)=(z^2/q s*z^2)/2 by ring]
    nlinarith only [est,pos]
  have low := intervalIntegral.integral_mono_on (μ:=volume) c.period_pos.le
    ((((ck.pow 2).const_mul A).sub continuous_const).intervalIntegrable ..) (cv.intervalIntegrable ..)
    (fun s _ => point s)
  change (∫s in 0..c.period,A*c.curvature s^2-m^3/4)≤_ at low
  rw [intervalIntegral.integral_sub (f:=fun s=>A*c.curvature s^2) (g:=fun _=>m^3/4)
    (((ck.pow 2).const_mul A).intervalIntegrable ..)
    (continuous_const.intervalIntegrable ..), intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    sub_zero,smul_eq_mul] at low
  have en : (∫s in 0..c.period,c.curvature s^2)=2*c.energy := by unfold energy; ring
  rw [en] at low
  dsimp only [A] at low
  change c.nodalSlopeMass b + _ - _ = 0 at ft
  linarith only [low,upper,ft,congrArg (fun z:ℝ=>m*z) rms]

end LengthGrowth.ClosedFrenetCurve
#print axioms LengthGrowth.ClosedFrenetCurve.energy_rms_le_nodal_force
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

def nodalUpperRate (t : ℝ) : ℝ := if ht : 0≤t then
  sInf {x | ∃ b : ℝ, 0<b ∧ x=Real.sqrt (c.length t*c.dissipation t)*
    ((c.regularPositionAt ht).closedFrenetCurve.nodalSlopeMass b+b*c.energy t)} else 0

private theorem nodal_feeding {t : ℝ} (ht : 0<t) {b : ℝ} (hb : 0<b) :
    c.energy t*c.lengthRate t-c.length t*c.dissipation t ≤
    Real.sqrt (c.length t*c.dissipation t)*
    ((c.regularPositionAt ht.le).closedFrenetCurve.nodalSlopeMass b+b*c.energy t) := by
  let p := (c.regularPositionAt ht.le).closedFrenetCurve
  let E := c.energy t
  let L := c.length t
  let D := c.dissipation t
  let m := Real.sqrt (2*E/L)
  let s := Real.sqrt (L*D)
  have lp : 0<L := c.length_pos ht.le
  have ep : 0<E := c.energy_pos ht.le
  have dp : 0≤D := c.dissipation_nonneg t
  have mp : 0≤m := Real.sqrt_nonneg _
  have sp : 0≤s := Real.sqrt_nonneg _
  have ss : s^2=L*D := Real.sq_sqrt (by positivity)
  have mm : m^2*L=2*E := by
    dsimp only [m]; rw [Real.sq_sqrt (by positivity),div_mul_cancel₀ _ lp.ne']
  have hE : p.energy=E := (c.regularPositionAt ht.le).closedFrenetCurve_energy
  have hD : p.dissipation=D := (c.regularPositionAt ht.le).closedFrenetCurve_dissipation
  have hL : p.period=L := rfl
  have geom := p.energy_rms_le_nodal_force hb mp (by rwa [hL,hE])
  rw [hE,hL,hD] at geom
  have ms : (m*s)^2=2*E*D := by rw [mul_pow,ss,←mul_assoc,mm]
  have rate : c.lengthRate t≤m*s := by
    apply le_of_sq_le_sq _ (mul_nonneg mp sp)
    rw [ms]; exact c.lengthRate_sq_le ht.le
  change E*c.lengthRate t-L*D≤s*_
  change E*m≤p.nodalSlopeMass b+b*E+s at geom
  linarith only [mul_le_mul_of_nonneg_left rate ep.le,mul_le_mul_of_nonneg_right geom sp,ss]

theorem deriv_product_le_nodalUpperRate (hf : c.IsNormalFEF) {t : ℝ} (ht : 0<t) :
    deriv c.normalizedProduct t≤c.nodalUpperRate t := by
  rw [nodalUpperRate,dif_pos ht.le,(c.normalizedProduct_hasDerivAt_normal hf ht).deriv]
  apply le_csInf
  · exact ⟨_,1,by norm_num,rfl⟩
  · rintro _ ⟨b,hb,rfl⟩
    exact c.nodal_feeding ht hb

theorem nodalUpperRate_nonneg (t : ℝ) : 0≤c.nodalUpperRate t := by
  unfold nodalUpperRate
  split
  next ht =>
    apply le_csInf
    · exact ⟨_,1,by norm_num,rfl⟩
    · rintro _ ⟨b,hb,rfl⟩
      let p := (c.regularPositionAt ht).closedFrenetCurve
      have hn : 0≤p.nodalSlopeMass b := intervalIntegral.integral_nonneg_of_forall
        p.period_pos.le (fun s=> by unfold LengthGrowth.ClosedFrenetCurve.nodalSlopeDensity; positivity)
      exact mul_nonneg (Real.sqrt_nonneg _) (add_nonneg hn (mul_nonneg hb.le (c.energy_nonneg t)))
  next => exact le_rfl

theorem quarter_bounds_of_integrable_rate_majorant (hf : c.IsNormalFEF) {T : ℝ} (tp : 0<T)
    (G : ℝ→ℝ) (nonneg : ∀t,0≤G t) (hi : IntegrableOn G (Ici T))
    (upper : ∀s,T≤s → deriv c.normalizedProduct s≤G s) :
    c.HasQuarterLengthBound ∧ c.HasQuarterEnergyBound := by
  let f := fun s => c.energy s*c.lengthRate s-c.length s*c.dissipation s
  have cf : ContinuousOn f (Ici 0) := (c.energy_continuousOn.mul c.lengthRate_continuousOn).sub
    (c.length_continuousOn.mul c.dissipation_continuousOn)
  obtain ⟨q,hq,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr tp.le)
    (c.normalizedProduct_continuousOn.mono (fun _ h=>h.1))
  let total := ∫s in Ici T,G s
  have total_pos : 0≤total := setIntegral_nonneg measurableSet_Ici (fun s _ => nonneg s)
  have bounded : c.HasBoundedEnergyLength := by
    refine ⟨c.normalizedProduct q+total,?_⟩
    intro t ht
    change c.normalizedProduct t≤_
    by_cases late : T≤t
    · have sub : Ioc T t ⊆ Ici T := fun _ h=>h.1.le
      have known (z : ℝ) (hz : z∈Icc T t) := c.normalizedProduct_hasDerivAt_normal hf (tp.trans_le hz.1)
      have intf : IntervalIntegrable f volume T t :=
        (cf.mono (fun _ (h : _∈Icc T t)=>tp.le.trans h.1)).intervalIntegrable_of_Icc late
      have ft := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=T) (b:=t)
        (fun z hz=>known z (by rwa [uIcc_of_le late] at hz)) intf
      have iG := (intervalIntegrable_iff_integrableOn_Ioc_of_le late).mpr (hi.mono_set sub)
      have dom := intervalIntegral.integral_mono_on (μ:=volume) late intf iG (fun s hs=> by
        have d := upper s hs.1
        rwa [(known s hs).deriv] at d)
      have cap := setIntegral_mono_set hi (Filter.Eventually.of_forall nonneg)
        (Filter.Eventually.of_forall sub)
      change (∫s in T..t,f s)=c.normalizedProduct t-c.normalizedProduct T at ft
      have qT := hmax (show T∈Icc (0:ℝ) T from ⟨tp.le,le_rfl⟩)
      change c.normalizedProduct T≤c.normalizedProduct q at qT
      change (∫s in Ioc T t,G s)≤total at cap
      rw [←intervalIntegral.integral_of_le late] at cap
      linarith only [qT,dom,ft,cap]
    · exact (hmax ⟨ht,le_of_not_ge late⟩).trans (le_add_of_nonneg_right total_pos)
  have L := (c.quarter_length_iff_bounded_energyLength hf).mpr bounded
  exact ⟨L,c.quarter_energy_of_quarter_length hf L⟩

/-- Finite total nodal feeding on any positive-time tail suffices for the
fourth-root length and energy bounds of the original physical flow. -/
theorem quarter_bounds_of_integrable_nodalUpperRate (hf : c.IsNormalFEF) {T : ℝ}
    (tp : 0<T) (hi : IntegrableOn c.nodalUpperRate (Ici T)) :
    c.HasQuarterLengthBound ∧ c.HasQuarterEnergyBound := by
  exact c.quarter_bounds_of_integrable_rate_majorant hf tp _ c.nodalUpperRate_nonneg hi
    (fun _ h=>c.deriv_product_le_nodalUpperRate hf (tp.trans_le h))

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.quarter_bounds_of_integrable_nodalUpperRate
