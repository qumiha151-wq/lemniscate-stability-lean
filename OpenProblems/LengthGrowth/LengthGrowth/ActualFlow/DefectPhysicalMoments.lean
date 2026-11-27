import LengthGrowth.ActualFlow.DefectCenteredCurvature
import LengthGrowth.ActualFlow.PhysicalSaturationGap

noncomputable section
open MeasureTheory
namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

/-- The arclength mean of the actual elastic force is half the cubic
curvature integral, by periodicity of the first curvature derivative. -/
theorem bending_force_mean :
    (∫ s in 0..c.period,c.force s)=(∫ s in 0..c.period,c.curvature s^3)/2 := by
  have f := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=c.period)
    (fun s _ => c.curvature₁_deriv s) (c.curvature₂_continuous.intervalIntegrable ..)
  have eq : c.curvature₁ c.period=c.curvature₁ 0 := by simpa using c.curvature₁_periodic 0
  rw [eq,sub_self] at f
  simp only [force]
  rw [intervalIntegral.integral_add (f:=c.curvature₂) (g:=fun s => c.curvature s^3/2)
    (c.curvature₂_continuous.intervalIntegrable ..)
    (((c.curvature_continuous.pow 3).div_const 2).intervalIntegrable ..),
    intervalIntegral.integral_div,f,zero_add]

/-- The two signed moment estimates follow simultaneously from a genuine
nonnegative product rate, without prescribing either moment by hand. -/
theorem bending_moment_inputs {μ R : ℝ} (hR : 0≤R)
    (mean : (∫ s in 0..c.period,c.curvature s)=c.period*μ)
    (scale : c.period*R^2=2*c.energy)
    (rate : c.period*c.dissipation≤c.energy*(∫ s in 0..c.period,c.curvature s*c.force s)) :
    2*(∫ s in 0..c.period,c.curvature s^3) ≤ (2*c.energy)*(μ+R) ∧
    4*Real.pi^2*(2*c.energy) ≤ 2*c.period^2*(∫ s in 0..c.period,c.curvature s*c.force s) := by
  let L := c.period
  let E := c.energy
  let J := ∫ s in 0..c.period,c.curvature s*c.force s
  let C := ∫ s in 0..c.period,c.curvature s^3
  let b := E/(2*L)
  have hp : 0<L := c.period_pos
  have ep : 0<E := c.energy_pos
  have bpos : 0≤b := by dsimp [b]; positivity
  have eb : 2*b*L=E := by dsimp [b]; field_simp
  change L*c.dissipation≤E*J at rate
  have mj : c.dissipation≤2*b*J := by
    apply le_of_mul_le_mul_left (a:=L) _ hp
    calc L*c.dissipation≤E*J := rate
         _ = L*(2*b*J) := by rw [←eb]; ring
  have sr := c.growthResidual_square
  change (∫ s in 0..c.period,c.growthResidual s^2)=c.dissipation-2*b*J+b^2*(2*E) at sr
  have bounded : (∫ s in 0..c.period,c.growthResidual s^2)≤b^2*(2*E) := by linarith
  have cs := interval_integral_mul_sq_le (f:=fun _ : ℝ => (1:ℝ)) continuous_const
    c.growthResidual_continuous c.period_pos.le
  have sc : (∫ s in 0..c.period,c.growthResidual s)^2 ≤ L*(∫ s in 0..c.period,c.growthResidual s^2) := by
    simpa [L] using cs
  have meanResidual : (∫ s in 0..c.period,c.growthResidual s)=C/2-b*(L*μ) := by
    unfold growthResidual
    rw [intervalIntegral.integral_sub (c.force_continuous.intervalIntegrable ..)
      ((c.curvature_continuous.const_mul _).intervalIntegrable ..),
      intervalIntegral.integral_const_mul,mean,c.bending_force_mean]
  rw [meanResidual] at sc
  have square : (C/2-b*(L*μ))^2≤(b*L*R)^2 := by
    calc
      _ ≤ L*(b^2*(2*E)) := sc.trans (mul_le_mul_of_nonneg_left bounded hp.le)
      _ = _ := by change c.period*(b^2*(2*c.energy))=(b*c.period*R)^2; rw [←scale]; ring
  have up := le_of_sq_le_sq square (show 0≤b*L*R by positivity)
  constructor
  · change 2*C≤(2*E)*(μ+R)
    linarith only [up,congrArg (fun z => z*μ) eb,congrArg (fun z => z*R) eb]
  · have sv := c.sharp_virial
    change 4*Real.pi^2*E^2 ≤ c.dissipation*L^3 at sv
    change 4*Real.pi^2*(2*E)≤2*L^2*J
    apply le_of_mul_le_mul_left (a:=E) _ ep
    linarith only [sv,mul_le_mul_of_nonneg_right rate (sq_nonneg L)]

end LengthGrowth.ClosedFrenetCurve
#print axioms LengthGrowth.ClosedFrenetCurve.bending_moment_inputs
