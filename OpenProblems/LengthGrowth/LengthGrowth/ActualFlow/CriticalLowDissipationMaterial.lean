import LengthGrowth.ActualFlow.CriticalLowDissipation
import LengthGrowth.ActualFlow.CriticalDensityMaterial
import LengthGrowth.ActualFlow.SharpVirial

noncomputable section
open Set Function MeasureTheory FreeElasticScalar
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.PeriodicRegularPosition

/-- Closedness gives a two-parameter necessary bound for the least
number of half-RMS excursion pieces at low normalized dissipation. -/
theorem critical_low_dissipation (p : PeriodicRegularPosition) (N : ℕ)
    (hn : p.CriticalDensityCount N) :
    let E:=materialEnergy p.position p.period
    let L:=p.length
    let d:=materialDissipation p.position p.period*L^2/(8*E^3)
    16*d≤1 → (2*(E*L))^2 ≤ (10^16:ℝ)*((N:ℝ)+1)^6*d := by
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
  change 16*d≤1 → (2*(E*L))^2 ≤ _*d
  intro low
  have normD : mass/P=d := by
    rw [mass_eq]
    dsimp only [d,a]
    rw [hEp]
    field_simp [hL.ne',hP.ne']
    ring
  have md : mass=d*P := (div_eq_iff hP.ne').mp normD
  have vir:=p.material_sharp_virial
  change 4*Real.pi^2*E^2 ≤ D*L^3 at vir
  have pi : 1≤Real.pi^2 := by nlinarith only [Real.pi_gt_three,sq_nonneg (Real.pi-3)]
  have ds : d*(8*E^3)=D*L^2 := div_mul_cancel₀ _ (by positivity)
  have vp : 1≤P*mass := by
    rw [md,show P*(d*P)=d*P^2 by ring,hp2]
    by_contra! hh
    nlinarith only [mul_lt_mul_of_pos_right hh (show 0<4*E^2 by positivity),
      mul_le_mul_of_nonneg_right pi (show 0≤4*E^2 by positivity),vir,congrArg (fun x:ℝ => x*L) ds]
  have low' : 16*mass≤P := by rw [md]; nlinarith only [mul_le_mul_of_nonneg_right low hP.le]
  have s:=CriticalDensity.low_dissipation_count hP (p.scaledArclengthCurvature_smooth a)
    (p.scaledArclengthCurvature_periodic hscale) rms N hn low' vp
  change P^5 ≤ (10^16:ℝ)*((N:ℝ)+1)^6*mass at s
  rw [←hp2]
  rw [md] at s
  apply (mul_le_mul_iff_left₀ hP).mp
  nlinarith only [s]

end LengthGrowth.ActualFlow.PeriodicRegularPosition
#print axioms LengthGrowth.ActualFlow.PeriodicRegularPosition.critical_low_dissipation
