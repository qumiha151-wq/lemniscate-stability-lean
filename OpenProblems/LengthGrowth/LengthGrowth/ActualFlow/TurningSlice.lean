import LengthGrowth.ActualFlow.CriticalLowDissipationMaterial

noncomputable section
open Set Function MeasureTheory FreeElasticScalar
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.PeriodicRegularPosition

/-- The signed turning on each normalized interval is the signed
turning on its corresponding genuine arclength interval. -/
theorem turning_on_scaled_interval (p : PeriodicRegularPosition) (a x y : ℝ) :
    (∫s in x..y,p.scaledArclengthCurvature a s)=
      ∫s in (a*x)..(a*y),p.closedFrenetCurve.curvature s := by
  unfold scaledArclengthCurvature
  rw [intervalIntegral.integral_const_mul]
  exact intervalIntegral.smul_integral_comp_mul_left _ _

/-- Rescaling arclength preserves total absolute turning. -/
theorem scaled_total_absolute_turn (p : PeriodicRegularPosition) {a P : ℝ}
    (ha : 0<a) (span : a*P=p.length) :
    (∫s in 0..P,|p.scaledArclengthCurvature a s|)=p.closedFrenetCurve.absoluteCurvature := by
  have h:=intervalIntegral.smul_integral_comp_mul_left
    (fun x=>|p.closedFrenetCurve.curvature x|) a (a:=0) (b:=P)
  simp only [smul_eq_mul,mul_zero,span] at h
  unfold scaledArclengthCurvature
  simp only [abs_mul,abs_of_pos ha,intervalIntegral.integral_const_mul]
  exact h

/-- The actual immersion supplies the period, force bound, RMS normalization
and sixth-power stress bound used to count macroscopic turning excursions. -/
theorem turning_slice_bounds (p : PeriodicRegularPosition) :
    let E := materialEnergy p.position p.period
    let L := p.length
    let D := materialDissipation p.position p.period
    let P := Real.sqrt (2*(E*L))
    let u := p.scaledArclengthCurvature (L/P)
    let d := D*L^2/(8*E^3)
    4*d≤1 → 0<P ∧ ContDiff ℝ ∞ u ∧ Periodic u P ∧
      (∫s in 0..P,u s^2)=P ∧ (∫s in 0..P, |FiniteSignWindow.force u s|)≤P/2 ∧
      ∃M : ℝ, 0≤M ∧ (∀s,|u s|≤M) ∧ M^6≤(2^23:ℝ)*P^2*d := by
  let E := materialEnergy p.position p.period
  let L := p.length
  let D := materialDissipation p.position p.period
  let P := Real.sqrt (2*(E*L))
  let a := L/P
  let u := p.scaledArclengthCurvature a
  let F := FiniteSignWindow.force u
  let mass := ∫s in 0..P, F s^2
  have hL : 0<L:=p.length_pos
  have hE : 0<E:=p.material_energy_pos
  have hP : 0<P := Real.sqrt_pos.mpr (by positivity)
  have hp2 : P^2=2*(E*L) := Real.sq_sqrt (by positivity)
  have ha : 0<a := div_pos hL hP
  have hscale : a*P=p.length := div_mul_cancel₀ L hP.ne'
  have mom:=p.scaledArclengthCurvature_moment ha hP hscale
  have cu:=mom 2 0
  have cf:=mom 0 2
  simp only [pow_zero,one_mul,mul_one] at cu cf
  have eint : (∫s in 0..p.period, curvature p.position s^2*speed p.position s) = 2*E := by
    dsimp only [E, materialEnergy]
    ring
  rw [eint] at cu
  change (∫s in 0..P,u s^2)/P=a^2/L*(2*E) at cu
  change (∫s in 0..P,(deriv (deriv u) s+(1/2:ℝ)*u s^3)^2)/P=(a^3)^2/L*D at cf
  have mass_eq : mass/P=(a^3)^2/L*D := by
    simpa only [mass,F,FiniteSignWindow.force,div_eq_inv_mul,mul_one] using cf
  have hEp : E=P^2/(2*L) := by
    apply (eq_div_iff (by positivity : 2*L≠0)).mpr
    linarith only [hp2]
  have rms : (∫s in 0..P, u s^2)=P := by
    have h:= (div_eq_iff hP.ne').mp cu
    rw [hEp] at h
    dsimp only [a] at h
    rw [h]
    field_simp [hP.ne',hL.ne']


  let d:=D*L^2/(8*E^3)
  change 4*d≤1 → 0<P ∧ ContDiff ℝ ∞ u ∧ Periodic u P ∧
    (∫s in 0..P,u s^2)=P ∧ (∫s in 0..P, |F s|)≤P/2 ∧
    ∃M : ℝ, 0≤M ∧ (∀s,|u s|≤M) ∧ M^6≤(2^23:ℝ)*P^2*d
  intro low
  have normD : mass/P=d := by
    rw [mass_eq]
    dsimp only [d,a]
    rw [hEp]
    field_simp [hL.ne',hP.ne']
    ring
  have md : mass=d*P := (div_eq_iff hP.ne').mp normD
  have ku : ContDiff ℝ ∞ u := p.scaledArclengthCurvature_smooth a
  have per : Periodic u P := p.scaledArclengthCurvature_periodic hscale
  have cf0 : Continuous F := FiniteSignWindow.force_continuous ku
  have cs:=LengthGrowth.interval_integral_mul_sq_le (f:=fun _:ℝ => (1:ℝ)) continuous_const cf0.abs hP.le
  simp only [one_mul,mul_one,one_pow,sq_abs,intervalIntegral.integral_const,smul_eq_mul,sub_zero] at cs
  change (∫s in 0..P,|F s|)^2≤P*mass at cs
  have capF : (∫s in 0..P,|F s|)≤P/2 := by
    by_contra! bad
    have z:=pow_lt_pow_left₀ bad (by linarith only [hP] : 0≤P/2) (by decide : 2≠0)
    rw [md] at cs
    nlinarith only [z,cs,mul_le_mul_of_nonneg_right low (sq_nonneg P)]
  obtain ⟨w,_,mx⟩:=isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hP.le) ku.continuous.abs.continuousOn
  refine ⟨hP,ku,per,rms,capF,|u w|,abs_nonneg _,?_,?_⟩
  · intro s
    obtain ⟨r,hr,eq⟩:=per.exists_mem_Ico₀ hP s
    exact (congrArg abs eq).le.trans (mx (show r∈Icc 0 P from ⟨hr.1,hr.2.le⟩))
  · have controls:=p.closedFrenetCurve.energy_dissipation_controls_curvature (a*w)
    rw [p.closedFrenetCurve_energy,p.closedFrenetCurve_dissipation] at controls
    change (1/16777216:ℝ)*|p.closedFrenetCurve.curvature (a*w)|^6≤E*D at controls
    have scale : (2^23:ℝ)*P^2*d=16777216*a^6*E*D := by
      dsimp only [a,d]
      rw [hEp]
      field_simp [hL.ne',hP.ne']
      ring
    change |a*p.closedFrenetCurve.curvature (a*w)|^6≤(2^23:ℝ)*P^2*d
    rw [abs_mul,abs_of_pos ha,mul_pow,scale]
    nlinarith only [mul_le_mul_of_nonneg_left controls (pow_nonneg ha.le 6)]

end LengthGrowth.ActualFlow.PeriodicRegularPosition
#print axioms LengthGrowth.ActualFlow.PeriodicRegularPosition.turning_slice_bounds
