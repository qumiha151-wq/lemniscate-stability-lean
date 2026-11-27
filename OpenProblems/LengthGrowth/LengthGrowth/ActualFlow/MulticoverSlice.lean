import LengthGrowth.ActualFlow.MulticoverSigned
import LengthGrowth.ActualFlow.CriticalRMSAdapter

noncomputable section
open MeasureTheory Function
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow
theorem PeriodicRegularPosition.multicover_dissipation (c : PeriodicRegularPosition) :
    let M:=|materialSignedCurvature c.position c.period|
    let E:=materialEnergy c.position c.period
    let P:=Real.sqrt (2*(E*c.length))
    M≤P ∧ (6≤M → M<P → P≤M+3/5 →
      M^4/1000*(P^2-M^2)<c.length^4*(c.length*materialDissipation c.position c.period-E*materialLengthRate c.position c.period)) := by
  let E:=materialEnergy c.position c.period
  let L:=c.length
  let P:=Real.sqrt (2*(E*L))
  let a:=L/P
  let u:=c.scaledArclengthCurvature a
  let v:=fun t=>deriv (deriv u) t+(1/2:ℝ)*u t^3
  let avg:=fun f:ℝ→ℝ=>(∫t in 0..P,f t)/P
  let S:=materialSignedCurvature c.position c.period
  let D:=materialDissipation c.position c.period
  let V:=materialLengthRate c.position c.period
  have hL : 0<L:=c.length_pos
  have hE : 0<E:=c.material_energy_pos
  have hb : 0<2*(E*L):=by positivity
  have hP : 0<P:=Real.sqrt_pos.mpr hb
  have hp2 : P^2=2*(E*L):=Real.sq_sqrt hb.le
  have hE' : E=P^2/(2*L):=by
    apply (eq_div_iff (by positivity : (2:ℝ)*L≠0)).mpr
    linarith only [hp2]
  have ha : 0<a:=div_pos hL hP
  have hap : a*P=c.length:=div_mul_cancel₀ L hP.ne'
  have moment:=c.scaledArclengthCurvature_moment ha hP hap
  have one:=moment 1 0
  have two:=moment 2 0
  have vv:=moment 0 2
  have uv:=moment 1 1
  simp only [pow_zero,pow_one,one_mul,mul_one] at one two vv uv
  change avg u=a/L*S at one
  change avg (fun t=>u t^2)=a^2/L*(∫s in 0..c.period,curvature c.position s^2*speed c.position s) at two
  change avg (fun t=>v t^2)=(a^3)^2/L*D at vv
  change avg (fun t=>u t*v t)=a*a^3/L*V at uv
  have eint : (∫s in 0..c.period,curvature c.position s^2*speed c.position s)=2*E:=by
    dsimp only [E,materialEnergy]
    ring
  have unit : avg (fun t=>u t^2)=1:=by
    rw [two,eint,hE']
    dsimp only [a]
    field_simp [hL.ne',hP.ne']
  have unit' : (∫t in 0..P,u t^2)=P:=by
    simpa using (div_eq_iff hP.ne').mp unit
  have sum : (∫t in 0..P,u t)=S:=by
    rw [show a/L*S=S/P by dsimp only [a];field_simp [hL.ne',hP.ne']] at one
    exact (div_left_inj' hP.ne').mp one
  have smooth:=c.scaledArclengthCurvature_smooth a
  have cs:=LengthGrowth.interval_integral_mul_sq_le smooth.continuous (continuous_const (y:=(1:ℝ))) hP.le
  change (∫t in 0..P,u t*1)^2≤(∫t in 0..P,u t^2)*(∫_ in 0..P,(1:ℝ)^2) at cs
  simp only [mul_one,one_pow,intervalIntegral.integral_const,sub_zero,smul_eq_mul,unit',sum] at cs
  change |S|≤P ∧ (6≤|S| → |S|<P → P≤|S|+3/5 → |S|^4/1000*(P^2-|S|^2)<L^4*(L*D-E*V))
  constructor
  · nlinarith only [cs,sq_abs S,hP,abs_nonneg S]
  intro six lo hi
  have strict:=LengthGrowth.Multicover.coercive_for_rms (six.trans lo.le) smooth
    (c.scaledArclengthCurvature_periodic hap) unit' (sum ▸ lo) (sum ▸ hi)
  change (1/2:ℝ)*(∫t in 0..P,u t*v t)+(P-|∫t in 0..P,u t|)/500<∫t in 0..P,v t^2 at strict
  rw [sum] at strict
  have loss : (P-|S|)/500/P<avg (fun t=>v t^2)-(1/2:ℝ)*avg (fun t=>u t*v t):=by
    dsimp only [avg]
    rw [← mul_div_assoc,← sub_div]
    apply (div_lt_div_iff_of_pos_right hP).mpr
    linarith only [strict]
  rw [vv,uv] at loss
  have eqn : (a^3)^2/L*D-(1/2:ℝ)*(a*a^3/L*V)=L^4*(L*D-E*V)/(P^2)^3:=by
    dsimp only [a]
    rw [hE']
    field_simp [hL.ne',hP.ne']
  rw [eqn] at loss
  have loss':=(lt_div_iff₀ (by positivity : 0<(P^2)^3)).mp loss
  have reduce : (P-|S|)/500/P*(P^2)^3=P^5*(P-|S|)/500:=by field_simp [hP.ne']
  rw [reduce] at loss'
  have a : |S|^4≤P^4:=pow_le_pow_left₀ (abs_nonneg _) lo.le 4
  have b : |S|^4*(P+|S|)≤P^4*(P+P):=mul_le_mul a (by linarith only [lo] : P+|S|≤P+P)
    (by linarith only [hP,abs_nonneg S]) (by positivity)
  have d:=mul_le_mul_of_nonneg_right b (sub_nonneg.mpr lo.le)
  linarith only [loss',d]

theorem PeriodicRegularPosition.multicover_slice (c : PeriodicRegularPosition) :
    let M:=|materialSignedCurvature c.position c.period|
    let E:=materialEnergy c.position c.period
    let P:=Real.sqrt (2*(E*c.length))
    M≤P ∧ (6≤M → M<P → P≤M+3/5 →
      E*materialLengthRate c.position c.period<c.length*materialDissipation c.position c.period) := by
  let M:=|materialSignedCurvature c.position c.period|
  let E:=materialEnergy c.position c.period
  let P:=Real.sqrt (2*(E*c.length))
  have h:=c.multicover_dissipation
  refine ⟨h.1,fun six lo hi=>?_⟩
  have q:=h.2 six lo hi
  change M^4/1000*(P^2-M^2)<c.length^4*(c.length*materialDissipation c.position c.period-E*materialLengthRate c.position c.period) at q
  have nn : 0≤P^2-M^2:=sub_nonneg.mpr (pow_le_pow_left₀ (abs_nonneg _) lo.le 2)
  have r:=(mul_nonneg (show 0≤M^4/1000 by positivity) nn).trans_lt q
  exact sub_pos.mp ((mul_pos_iff_of_pos_left (pow_pos c.length_pos 4)).mp r)
end LengthGrowth.ActualFlow
#print axioms LengthGrowth.ActualFlow.PeriodicRegularPosition.multicover_dissipation

