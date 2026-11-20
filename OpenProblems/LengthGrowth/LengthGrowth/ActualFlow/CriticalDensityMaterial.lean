import LengthGrowth.ActualFlow.CriticalDensityScalar

noncomputable section
open Set Function MeasureTheory FreeElasticScalar
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.PeriodicRegularPosition

/-- At the length scale at which RMS curvature is one, each subarc of
one period has a partition into at most N+1 half-RMS excursion pieces. -/
def CriticalDensityCount (p : PeriodicRegularPosition) (N : ℕ) : Prop :=
  let P:=Real.sqrt (2*(materialEnergy p.position p.period*p.length))
  CriticalDensity.Count (p.scaledArclengthCurvature (p.length/P)) P N

/-- The sharp sign-density lower bound expressed in actual arclength,
physical elastic dissipation, and the bending energy of this immersion. -/
theorem criticalDensity_dissipation_bound (p : PeriodicRegularPosition) (N : ℕ)
    (hn : p.CriticalDensityCount N) :
    Real.sqrt (materialEnergy p.position p.period*p.length) ≤
      Real.sqrt (materialDissipation p.position p.period*p.length^3 /
        (2*(materialEnergy p.position p.period)^2)) + 2048*((N:ℝ)+1)*Real.sqrt ((N:ℝ)+1) := by
  let E := materialEnergy p.position p.period
  let L := p.length
  let D := materialDissipation p.position p.period
  let P := Real.sqrt (2*(E*L))
  let a := L/P
  let u := p.scaledArclengthCurvature a
  let F := FiniteSignWindow.force u
  let mass := ∫s in 0..P, F s^2
  let m : ℝ := (N:ℝ)+1
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
  have sharp:=CriticalDensity.scalar_bound hP (p.scaledArclengthCurvature_smooth a)
    (p.scaledArclengthCurvature_periodic hscale) rms N hn
  change P/2 ≤ Real.sqrt (P*mass)+1024*m*Real.sqrt m at sharp
  have orient : D*L^3/(2*E^2)=2*(P*mass) := by
    have h:=(div_eq_iff hP.ne').mp mass_eq
    rw [h,hEp]
    dsimp only [a]
    field_simp [hL.ne',hP.ne']
  have root : Real.sqrt (D*L^3/(2*E^2))=Real.sqrt 2*Real.sqrt (P*mass) := by
    rw [orient,Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  have root2 : Real.sqrt 2*(P/2)=Real.sqrt (E*L) := by
    change Real.sqrt 2*(Real.sqrt (2*(E*L))/2)=_
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    nlinarith only [congrArg (fun t : ℝ=>t*Real.sqrt (E*L)) (Real.sq_sqrt (by norm_num : (0:ℝ)≤2))]
  have hm : 0≤m := by dsimp [m];positivity
  have hs2 : Real.sqrt 2≤2 := (Real.sqrt_le_iff).mpr (by norm_num)
  have scaled := mul_le_mul_of_nonneg_left sharp (Real.sqrt_nonneg 2)
  rw [root2,mul_add,←root] at scaled
  change Real.sqrt (E*L) ≤ Real.sqrt (D*L^3/(2*E^2))+2048*m*Real.sqrt m
  nlinarith only [scaled,mul_le_mul_of_nonneg_right hs2 (mul_nonneg hm (Real.sqrt_nonneg m))]

end LengthGrowth.ActualFlow.PeriodicRegularPosition
#print axioms LengthGrowth.ActualFlow.PeriodicRegularPosition.criticalDensity_dissipation_bound
