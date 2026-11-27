import SolitonClassification.MulticoverSigned
import SolitonClassification.LowBendingArclength

noncomputable section
open Set MeasureTheory Function
namespace ClosedSimilarity.LowBending.ClosedFrenetCurve
open ClosedSimilarity.MultiBending
variable (c : ClosedFrenetCurve)

/-- The RMS normalization of the curvature uses the actual derivative
fields of this arclength-parametrized curve. No independent norm or
rescaled forcing is assumed. -/
theorem multi_bending_slice :
    let S := |∫ s in 0..c.period,c.curvature s|
    let P := Real.sqrt (2*c.energy*c.period)
    S≤P ∧ (6≤S → S<P → P≤S+3/5 →
      c.energy*(∫ s in 0..c.period,c.curvature s*c.force s)<c.period*c.dissipation) := by
  let L := c.period
  let E := c.energy
  let P := Real.sqrt (2*E*L)
  let a := L/P
  let S := ∫s in 0..L,c.curvature s
  let V := ∫s in 0..L,c.curvature s*c.force s
  let Y := c.dissipation
  have lp : 0<L := c.period_pos
  have ep : 0<E := c.energy_pos
  have bp : 0<2*E*L := by positivity
  have pp : 0<P := Real.sqrt_pos.mpr bp
  have psq : P^2=2*E*L := Real.sq_sqrt bp.le
  have ap : 0<a := div_pos lp pp
  have period : a*P=L := div_mul_cancel₀ L pp.ne'
  have energy : (∫s in 0..L,c.curvature s^2)=2*E := by dsimp [E,energy,L];ring
  have cs := LowBending.interval_integral_mul_sq_le c.curvature_continuous (continuous_const (y:=(1:ℝ))) lp.le
  simp only [mul_one,one_pow,intervalIntegral.integral_const,sub_zero,smul_eq_mul,energy] at cs
  change |S|≤P ∧ (6≤|S| → |S|<P → P≤|S|+3/5 → E*V<L*Y)
  constructor
  · change S^2≤2*E*L at cs
    nlinarith only [cs,psq,sq_abs S,abs_nonneg S,pp]
  intro six lo hi
  let U : Fn := ⟨fun t=>a*c.curvature (a*t),continuous_const.mul
    (c.curvature_continuous.comp (continuous_const.mul continuous_id))⟩
  let D : Fn := ⟨fun t=>a^2*c.curvature₁ (a*t),continuous_const.mul
    (c.curvature₁_continuous.comp (continuous_const.mul continuous_id))⟩
  let Q : Fn := ⟨fun t=>a^3*c.curvature₂ (a*t),continuous_const.mul
    (c.curvature₂_continuous.comp (continuous_const.mul continuous_id))⟩
  let F := normalizedForce U Q
  have du (t : ℝ) : HasDerivAt U (D t) t := by
    apply (((c.curvature_deriv (a*t)).comp t ((hasDerivAt_id t).const_mul a)).const_mul a).congr_deriv
    dsimp only [D,ContinuousMap.coe_mk];ring
  have dd (t : ℝ) : HasDerivAt D (Q t) t := by
    apply (((c.curvature₁_deriv (a*t)).comp t ((hasDerivAt_id t).const_mul a)).const_mul (a^2)).congr_deriv
    dsimp only [Q,ContinuousMap.coe_mk];ring
  have pu : Periodic U P := fun t=>by
    change a*c.curvature (a*(t+P))=_
    rw [mul_add,period,c.curvature_periodic]
    rfl
  have pd : Periodic D P := fun t=>by
    change a^2*c.curvature₁ (a*(t+P))=_
    rw [mul_add,period,c.curvature₁_periodic]
    rfl
  have scale (f : ℝ→ℝ) (q : ℝ) :
      (∫s in 0..P,q*f (a*s))=(q/a)*(∫s in 0..L,f s) := by
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_mul_left f ap.ne',mul_zero,period,smul_eq_mul]
    ring
  have sum : mass P U=S := by
    change (∫s in 0..P,a*c.curvature (a*s))=_
    rw [scale,div_self ap.ne',one_mul]
  have unit : mass P (U^2)=P := by
    change (∫s in 0..P,(a*c.curvature (a*s))^2)=_
    simp_rw [mul_pow]
    rw [scale (fun u=>c.curvature u^2),energy]
    have h : a^2/a=a := by field_simp
    rw [h]
    dsimp only [a]
    field_simp [pp.ne']
    linarith only [psq]
  have force (t : ℝ) : F t=a^3*c.force (a*t) := by
    change a^3*c.curvature₂ (a*t)+(1/2:ℝ)*(a*c.curvature (a*t))^3=a^3*(c.curvature₂ (a*t)+c.curvature (a*t)^3/2)
    ring
  have squared : mass P (F^2)=(a^6/a)*Y := by
    change (∫s in 0..P,F s^2)=_
    simp_rw [force,mul_pow,←pow_mul]
    exact scale (fun s=>c.force s^2) _
  have mixed : mass P (U*F)=(a^4/a)*V := by
    change (∫s in 0..P,(a*c.curvature (a*s))*F s)=_
    simp_rw [force,show ∀z w:ℝ,(a*z)*(a^3*w)=a^4*(z*w) by intros;ring]
    exact scale (fun s=>c.curvature s*c.force s) _
  have rate := signed_record P (six.trans lo.le) U D Q pu pd du dd unit (sum ▸ lo) (sum ▸ hi)
  change (1/2:ℝ)*mass P (U*F)<mass P (F^2) at rate
  rw [mixed,squared] at rate
  have loss : 0<(a^6/a)*Y-(1/2:ℝ)*((a^4/a)*V) := sub_pos.mpr rate
  have eqE : E=P^2/(2*L) := by apply (eq_div_iff (by positivity : (2:ℝ)*L≠0)).mpr; linarith only [psq]
  have eq : (a^6/a)*Y-(1/2:ℝ)*((a^4/a)*V)=L^4*(L*Y-E*V)/P^5 := by
    rw [eqE]; dsimp only [a];field_simp [pp.ne',lp.ne']
  rw [eq] at loss
  exact sub_pos.mp ((mul_pos_iff_of_pos_left (by positivity : 0<L^4)).mp
    ((div_pos_iff_of_pos_right (by positivity : 0<P^5)).mp loss))

end ClosedSimilarity.LowBending.ClosedFrenetCurve
#print axioms ClosedSimilarity.LowBending.ClosedFrenetCurve.multi_bending_slice
