import LengthGrowth.ActualFlow.EnclosingDisk

noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

/-- The normal part of dilation, plus any infinitesimal translation and rotation. -/
def similaritySupport (z : ℂ) (ω s : ℝ) : ℝ :=
  inner ℝ (c.normal s) ((1+(ω:ℂ)*Complex.I)*c.curve s-z)

def growthResidual (s : ℝ) : ℝ := c.force s-c.energy/(2*c.period)*c.curvature s

theorem similaritySupport_continuous (z : ℂ) (ω : ℝ) : Continuous (c.similaritySupport z ω) :=
  (continuous_const.mul c.tangent_continuous : Continuous c.normal).inner
    ((continuous_const.mul (continuous_iff_continuousAt.mpr fun s => (c.curve_deriv s).continuousAt)).sub
      continuous_const)

theorem growthResidual_continuous : Continuous c.growthResidual :=
  c.force_continuous.sub (c.curvature_continuous.const_mul _)

theorem growthResidual_similarity_virial (z : ℂ) (ω : ℝ) :
    (∫s in 0..c.period,c.growthResidual s*c.similaritySupport z ω s) = -c.energy/2 := by
  let b := c.energy/(2*c.period)
  let a : ℂ := 1+(ω:ℂ)*Complex.I
  let w := fun s => c.stress s-(b:ℂ)*c.tangent s
  let v := fun s => a*c.curve s-z
  let q := fun s => c.growthResidual s*c.similaritySupport z ω s
  have hq : Continuous q := c.growthResidual_continuous.mul (c.similaritySupport_continuous z ω)
  have dw (s : ℝ) : HasDerivAt w ((c.growthResidual s:ℂ)*c.normal s) s := by
    apply ((c.stress_deriv s).sub ((c.tangent_deriv s).const_mul (b:ℂ))).congr_deriv
    simp only [growthResidual,Complex.ofReal_sub,Complex.ofReal_mul]
    change _ = ((c.force s:ℂ)-(b:ℂ)*(c.curvature s:ℂ))*c.normal s
    dsimp [normal]
    ring
  have dv (s : ℝ) : HasDerivAt v (a*c.tangent s) s := ((c.curve_deriv s).const_mul a).sub_const z
  have tan (s : ℝ) : inner ℝ (w s) (a*c.tangent s) =
      c.curvature s^2/2-b+ω*c.curvature₁ s := by
    change (a*c.tangent s*conj (c.stress s-(b:ℂ)*c.tangent s)).re=_
    rw [map_sub,map_mul,Complex.conj_ofReal]
    have sw : a*c.tangent s*(conj (c.stress s)-(b:ℂ)*conj (c.tangent s))=
        a*(c.tangent s*conj (c.stress s)-(b:ℂ)*(c.tangent s*conj (c.tangent s))) := by ring
    have h1 := c.tangent_mul_star_stress s
    have h2 := c.tangent_mul_star s
    change c.tangent s*conj (c.stress s)=_ at h1
    change c.tangent s*conj (c.tangent s)=_ at h2
    rw [sw,h1,h2,mul_one]
    dsimp [a]
    simp [Complex.mul_re,Complex.mul_im,←Complex.ofReal_pow]
  have derivB (s : ℝ) : HasDerivAt
      (fun x => inner ℝ (w x) (v x)-ω*c.curvature x)
      (q s+(c.curvature s^2/2-b)) s := by
    apply (((dw s).inner ℝ (dv s)).sub ((c.curvature_deriv s).const_mul ω)).congr_deriv
    rw [←Complex.real_smul,real_inner_smul_left,tan]
    change _ = c.growthResidual s*inner ℝ (c.normal s) (v s)+(c.curvature s^2/2-b)
    ring
  have hk := (c.curvature_continuous.pow 2).div_const 2
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=c.period)
    (fun s _ => derivB s) ((hq.add (hk.sub continuous_const)).intervalIntegrable _ _)
  have sw := c.stress_periodic 0
  have tw := c.tangent_periodic 0
  have xw := c.curve_periodic 0
  have kw := c.curvature_periodic 0
  simp only [zero_add] at sw tw xw kw
  dsimp only [w,v] at h
  rw [sw,tw,xw,kw,sub_self,intervalIntegral.integral_add (f:=q)
    (g:=fun s => c.curvature s^2/2-b) (hq.intervalIntegrable _ _)
    ((hk.sub continuous_const).intervalIntegrable _ _),intervalIntegral.integral_sub
    (f:=fun s => c.curvature s^2/2) (g:=fun _ => b)
    (hk.intervalIntegrable _ _) intervalIntegrable_const,intervalIntegral.integral_const,
    sub_zero,smul_eq_mul,intervalIntegral.integral_div] at h
  have bL : c.period*b=c.energy/2 := by dsimp [b]; field_simp [c.period_pos.ne']
  rw [bL] at h
  change (∫s in 0..c.period,q s) = -c.energy/2
  change (∫s in 0..c.period,q s)+(c.energy-c.energy/2)=0 at h
  linarith

theorem growthResidual_support_cost (z : ℂ) (ω : ℝ) :
    (c.energy/2)^2 ≤ (∫s in 0..c.period,c.growthResidual s^2)*
      (∫s in 0..c.period,c.similaritySupport z ω s^2) := by
  have h := interval_integral_mul_sq_le c.growthResidual_continuous
    (c.similaritySupport_continuous z ω) c.period_pos.le
  rw [c.growthResidual_similarity_virial] at h
  nlinarith only [h]

theorem centered_support_moment_le :
    (2*Real.pi)^2*(∫s in 0..c.period,c.similaritySupport c.arclengthCentroid 0 s^2) ≤ c.period^3 := by
  let y := fun s => c.curve s-c.arclengthCentroid
  have cc : Continuous c.curve := continuous_iff_continuousAt.mpr fun s => (c.curve_deriv s).continuousAt
  have hy : Continuous y := cc.sub continuous_const
  have hz : (∫s in 0..c.period,y s)=0 := by
    unfold y arclengthCentroid
    rw [intervalIntegral.integral_sub (cc.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const,sub_zero,smul_smul,mul_inv_cancel₀ c.period_pos.ne',one_smul,sub_self]
  have hw := periodic_wirtinger c.period_pos y c.tangent
    (by dsimp [y]; rw [show c.curve c.period=c.curve 0 by simpa using c.curve_periodic 0])
    (fun s => (c.curve_deriv s).sub_const _) c.tangent_continuous hz
  have hp := c.similaritySupport_continuous c.arclengthCentroid 0
  have hm : (∫s in 0..c.period,c.similaritySupport c.arclengthCentroid 0 s^2) ≤
      ∫s in 0..c.period,‖y s‖^2 := by
    apply intervalIntegral.integral_mono_on c.period_pos.le ((hp.pow 2).intervalIntegrable _ _)
      ((hy.norm.pow 2).intervalIntegrable _ _)
    intro s _
    have hi := abs_real_inner_le_norm (c.normal s) (y s)
    rw [c.normal_unit,one_mul] at hi
    simpa [similaritySupport,y] using pow_le_pow_left₀ (abs_nonneg _) hi 2
  simp [c.tangent_unit] at hw
  nlinarith only [hw,mul_le_mul_of_nonneg_left hm (sq_nonneg (2*Real.pi))]

theorem growthResidual_sharp_cost :
    Real.pi^2*c.energy^2 ≤ (∫s in 0..c.period,c.growthResidual s^2)*c.period^3 := by
  have hc := c.growthResidual_support_cost c.arclengthCentroid 0
  have hr := intervalIntegral.integral_nonneg_of_forall (μ:=volume) c.period_pos.le
    (fun s => sq_nonneg (c.growthResidual s))
  nlinarith only [mul_le_mul_of_nonneg_left hc (sq_nonneg (2*Real.pi)),
    mul_le_mul_of_nonneg_left c.centered_support_moment_le hr]
end LengthGrowth.ClosedFrenetCurve

#print axioms LengthGrowth.ClosedFrenetCurve.growthResidual_similarity_virial
#print axioms LengthGrowth.ClosedFrenetCurve.growthResidual_sharp_cost
