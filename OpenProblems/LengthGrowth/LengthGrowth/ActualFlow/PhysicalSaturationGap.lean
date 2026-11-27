import LengthGrowth.ActualFlow.SaturationSupport
import LengthGrowth.ActualFlow.NormalizedProduct

noncomputable section
open MeasureTheory Set
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

def optimalSimilarityMoment : ℝ := sInf {m | ∃ (z : ℂ) (ω : ℝ),
  m=∫s in 0..c.period,c.similaritySupport z ω s^2}

theorem growthResidual_optimal_cost :
    (c.energy/2)^2 ≤ (∫s in 0..c.period,c.growthResidual s^2)*c.optimalSimilarityMoment := by
  let m := ∫s in 0..c.period,c.growthResidual s^2
  have hp : 0<m := by
    have h := c.growthResidual_sharp_cost
    have pos : 0<Real.pi^2*c.energy^2 := by have := c.energy_pos; positivity
    exact pos_of_mul_pos_left (pos.trans_le h) (pow_nonneg c.period_pos.le 3)
  rw [mul_comm]
  apply (div_le_iff₀ hp).mp
  apply le_csInf
  · exact ⟨_,0,0,rfl⟩
  · rintro x ⟨z,ω,rfl⟩
    apply (div_le_iff₀ hp).mpr
    rw [mul_comm]
    exact c.growthResidual_support_cost z ω

theorem growthResidual_square :
    (∫s in 0..c.period,c.growthResidual s^2) = c.dissipation -
      (2*(c.energy/(2*c.period)))*(∫s in 0..c.period,c.curvature s*c.force s)+
      (c.energy/(2*c.period))^2*(2*c.energy) := by
  let b := c.energy/(2*c.period)
  have hk := c.curvature_continuous
  have hf := c.force_continuous
  have mixed := (hk.mul hf).const_mul (2*b)
  have curv := (hk.pow 2).const_mul (b^2)
  have point (s:ℝ) : c.growthResidual s^2 = c.force s^2 -
      (2*b)*(c.curvature s*c.force s)+b^2*c.curvature s^2 := by
    dsimp [growthResidual,b]
    ring
  simp_rw [point]
  rw [intervalIntegral.integral_add (f:=fun s => c.force s^2-2*b*(c.curvature s*c.force s))
    (g:=fun s => b^2*c.curvature s^2) (((hf.pow 2).sub mixed).intervalIntegrable _ _) (curv.intervalIntegrable _ _),
    intervalIntegral.integral_sub (f:=fun s => c.force s^2) (g:=fun s => 2*b*(c.curvature s*c.force s))
      ((hf.pow 2).intervalIntegrable _ _) (mixed.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  unfold energy dissipation
  dsimp [b]
  unfold energy
  ring
end LengthGrowth.ClosedFrenetCurve

namespace LengthGrowth.ActualFlow.PeriodicRegularPosition
variable (p : PeriodicRegularPosition)
theorem arclength_integral_curvature_force :
    (∫s in 0..p.closedFrenetCurve.period,p.closedFrenetCurve.curvature s*p.closedFrenetCurve.force s) =
      materialLengthRate p.position p.period := by
  simp_rw [p.closedFrenetCurve_curvature,p.closedFrenetCurve_force,p.closedFrenetCurve_period]
  exact p.integral_comp_inverse
    ((curvature_smooth p.smooth p.regular).continuous.mul (force_smooth p.smooth p.regular).continuous)
end LengthGrowth.ActualFlow.PeriodicRegularPosition

namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- The actual dimensionless physical rate of the energy–length product. -/
def productGrowthFraction (t : ℝ) := c.length t*deriv c.normalizedProduct t/c.energy t^3

theorem productGrowthFraction_residual (hf : c.IsNormalFEF) {t : ℝ} (ht : 0<t) :
    let p := (c.regularPositionAt ht.le).closedFrenetCurve
    1/2-c.productGrowthFraction t = c.length t^2/c.energy t^3 * (∫s in 0..p.period,p.growthResidual s^2) := by
  let p := c.regularPositionAt ht.le
  have hE : p.closedFrenetCurve.energy=c.energy t := p.closedFrenetCurve_energy
  have hD : p.closedFrenetCurve.dissipation=c.dissipation t := p.closedFrenetCurve_dissipation
  have hL : p.closedFrenetCurve.period=c.length t := rfl
  have hC : (∫s in 0..p.closedFrenetCurve.period,p.closedFrenetCurve.curvature s*p.closedFrenetCurve.force s)
      = c.lengthRate t := p.arclength_integral_curvature_force
  have eq := p.closedFrenetCurve.growthResidual_square
  rw [hC,hE,hD,hL] at eq
  change 1/2-c.productGrowthFraction t = c.length t^2/c.energy t^3 *
    (∫s in 0..c.length t,p.closedFrenetCurve.growthResidual s^2)
  rw [eq,productGrowthFraction,(c.normalizedProduct_hasDerivAt_normal hf ht).deriv]
  have lp : 0<c.length t := p.length_pos
  field_simp [(c.energy_pos ht.le).ne',lp.ne']
  ring

theorem productGrowthFraction_optimal_moment (hf : c.IsNormalFEF) {t : ℝ} (ht : 0<t) :
    c.length t^2/(4*c.energy t) ≤ (1/2-c.productGrowthFraction t)*
      (c.regularPositionAt ht.le).closedFrenetCurve.optimalSimilarityMoment := by
  let p := (c.regularPositionAt ht.le).closedFrenetCurve
  have hE : p.energy=c.energy t := (c.regularPositionAt ht.le).closedFrenetCurve_energy
  have cost := p.growthResidual_optimal_cost
  rw [hE] at cost
  rw [c.productGrowthFraction_residual hf ht]
  have ep := c.energy_pos ht.le
  change c.length t^2/(4*c.energy t) ≤ (c.length t^2/c.energy t^3*
    (∫s in 0..p.period,p.growthResidual s^2))*p.optimalSimilarityMoment
  rw [mul_assoc,show c.length t^2/(4*c.energy t)=c.length t^2/c.energy t^3*(c.energy t/2)^2 by
    field_simp [ep.ne']; ring]
  exact mul_le_mul_of_nonneg_left cost (by positivity)

theorem productGrowthFraction_support_moment (hf : c.IsNormalFEF) {t : ℝ} (ht : 0<t)
    (z : ℂ) (ω : ℝ) :
    let p := (c.regularPositionAt ht.le).closedFrenetCurve
    c.length t^2/(4*c.energy t) ≤ (1/2-c.productGrowthFraction t)*
      (∫s in 0..p.period,p.similaritySupport z ω s^2) := by
  let p := (c.regularPositionAt ht.le).closedFrenetCurve
  have ep := c.energy_pos ht.le
  have hE : p.energy=c.energy t := (c.regularPositionAt ht.le).closedFrenetCurve_energy
  have cost := p.growthResidual_support_cost z ω
  rw [hE] at cost
  change c.length t^2/(4*c.energy t) ≤ (1/2-c.productGrowthFraction t)*_
  rw [c.productGrowthFraction_residual hf ht]
  change c.length t^2/(4*c.energy t) ≤ (c.length t^2/c.energy t^3*
    (∫s in 0..p.period,p.growthResidual s^2))*(∫s in 0..p.period,p.similaritySupport z ω s^2)
  rw [mul_assoc,show c.length t^2/(4*c.energy t)=c.length t^2/c.energy t^3*(c.energy t/2)^2 by
    field_simp [ep.ne']; ring]
  exact mul_le_mul_of_nonneg_left cost (by positivity)

theorem productGrowthFraction_le_pi_gap (hf : c.IsNormalFEF) {t : ℝ} (ht : 0<t) :
    c.productGrowthFraction t ≤ 1/2-Real.pi^2/c.normalizedProduct t := by
  let p := (c.regularPositionAt ht.le).closedFrenetCurve
  have hE : p.energy=c.energy t := (c.regularPositionAt ht.le).closedFrenetCurve_energy
  have hL : p.period=c.length t := rfl
  let r := ∫s in 0..p.period,p.growthResidual s^2
  have cost : Real.pi^2*c.energy t^2 ≤ r*c.length t^3 := by
    simpa only [hE,hL,r] using p.growthResidual_sharp_cost
  have ep := c.energy_pos ht.le
  have lp : 0<c.length t := p.period_pos
  have gap : Real.pi^2/(c.energy t*c.length t) ≤ c.length t^2/c.energy t^3*r := by
    field_simp [ep.ne',lp.ne']
    nlinarith only [cost,mul_le_mul_of_nonneg_left cost ep.le]
  change Real.pi^2/(c.energy t*c.length t) ≤ c.length t^2/c.energy t^3*_ at gap
  rw [←c.productGrowthFraction_residual hf ht] at gap
  change c.productGrowthFraction t ≤ 1/2-Real.pi^2/(c.energy t*c.length t)
  linarith
end LengthGrowth.ActualFlow.ForwardImmersion

#print axioms LengthGrowth.ActualFlow.ForwardImmersion.productGrowthFraction_residual
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.productGrowthFraction_optimal_moment
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.productGrowthFraction_le_pi_gap
