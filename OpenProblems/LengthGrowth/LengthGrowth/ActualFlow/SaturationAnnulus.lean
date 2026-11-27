import LengthGrowth.ActualFlow.PhysicalSaturationGap
import LengthGrowth.IntervalOscillation

noncomputable section
open Set MeasureTheory
open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

def radialTangentSupport (s : ℝ) := inner ℝ (c.tangent s) (c.curve s-c.arclengthCentroid)

theorem radialTangentSupport_continuous : Continuous c.radialTangentSupport :=
  c.tangent_continuous.inner
    ((continuous_iff_continuousAt.mpr fun s => (c.curve_deriv s).continuousAt).sub continuous_const)

theorem centered_support_pythagoras (s : ℝ) :
    c.radialTangentSupport s^2+c.similaritySupport c.arclengthCentroid 0 s^2 =
      ‖c.curve s-c.arclengthCentroid‖^2 := by
  let y := c.curve s-c.arclengthCentroid
  let w := y*conj (c.tangent s)
  have t : c.radialTangentSupport s=w.re := rfl
  have n : c.similaritySupport c.arclengthCentroid 0 s=w.im := by
    simp only [similaritySupport,Complex.ofReal_zero,zero_mul,add_zero,one_mul]
    change (y*conj (Complex.I*c.tangent s)).re=_
    rw [map_mul,Complex.conj_I,show y*(-Complex.I*conj (c.tangent s))=w*(-Complex.I) by dsimp [w]; ring]
    simp [Complex.mul_re]
  have weight : ‖w‖=‖y‖ := by simp [w,c.tangent_unit]
  rw [t,n,←weight]
  rw [←Complex.normSq_eq_norm_sq]
  change w.re^2+w.im^2=w.re*w.re+w.im*w.im
  ring

theorem centered_tangent_and_normal_moments :
    (2*Real.pi)^2*((∫s in 0..c.period,c.radialTangentSupport s^2)+
      (∫s in 0..c.period,c.similaritySupport c.arclengthCentroid 0 s^2))≤c.period^3 := by
  let y := fun s => c.curve s-c.arclengthCentroid
  have cc : Continuous c.curve := continuous_iff_continuousAt.mpr fun s => (c.curve_deriv s).continuousAt
  have hz : (∫s in 0..c.period,y s)=0 := by
    unfold y arclengthCentroid
    rw [intervalIntegral.integral_sub (cc.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const,sub_zero,smul_smul,mul_inv_cancel₀ c.period_pos.ne',one_smul,sub_self]
  have hw := periodic_wirtinger c.period_pos y c.tangent
    (by dsimp [y]; rw [show c.curve c.period=c.curve 0 by simpa using c.curve_periodic 0])
    (fun s => (c.curve_deriv s).sub_const _) c.tangent_continuous hz
  rw [←intervalIntegral.integral_add (f:=fun s => c.radialTangentSupport s^2)
    (g:=fun s => c.similaritySupport c.arclengthCentroid 0 s^2)
    ((c.radialTangentSupport_continuous.pow 2).intervalIntegrable _ _)
    (((c.similaritySupport_continuous _ _).pow 2).intervalIntegrable _ _)]
  simp_rw [c.centered_support_pythagoras]
  simpa [y,c.tangent_unit,pow_succ] using hw

theorem radialTangentSupport_oscillation {s t : ℝ} (hs : s∈Icc 0 c.period) (ht : t∈Icc 0 c.period) :
    (‖c.curve s-c.arclengthCentroid‖^2-‖c.curve t-c.arclengthCentroid‖^2)^2 ≤
      4*c.period*(∫x in 0..c.period,c.radialTangentSupport x^2) := by
  let y := fun s => c.curve s-c.arclengthCentroid
  have d (x : ℝ) : HasDerivAt (fun w => inner ℝ (y w) (y w)) (2*c.radialTangentSupport x) x := by
    have dy := (c.curve_deriv x).sub_const c.arclengthCentroid
    apply (dy.inner ℝ dy).congr_deriv
    change inner ℝ (y x) (c.tangent x)+inner ℝ (c.tangent x) (y x)=2*inner ℝ (c.tangent x) (y x)
    linarith only [real_inner_comm (y x) (c.tangent x)]
  have o := interval_oscillation_le d (c.radialTangentSupport_continuous.const_mul 2) hs ht
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,abs_mul,show |(2:ℝ)|=2 by norm_num,
    intervalIntegral.integral_const_mul] at o
  have sq := pow_le_pow_left₀ (abs_nonneg _) o 2
  have cs := interval_integral_mul_sq_le c.radialTangentSupport_continuous.abs
    (continuous_const : Continuous (fun _ : ℝ => (1:ℝ))) c.period_pos.le
  simp only [mul_one,sq_abs,one_pow,intervalIntegral.integral_const,sub_zero,smul_eq_mul] at cs
  rw [sq_abs] at sq
  dsimp [y] at sq
  nlinarith only [sq,cs]

/-- Stability at the sharp product gap. The integral refers to actual growth residual. -/
theorem growthResidual_centroid_annulus {s t : ℝ} (hs : s∈Icc 0 c.period) (ht : t∈Icc 0 c.period) :
    let r := ∫x in 0..c.period,c.growthResidual x^2
    Real.pi^2*r*(‖c.curve s-c.arclengthCentroid‖^2-‖c.curve t-c.arclengthCentroid‖^2)^2 ≤
      r*c.period^4-Real.pi^2*c.energy^2*c.period := by
  let r := ∫x in 0..c.period,c.growthResidual x^2
  have hr : 0≤r := intervalIntegral.integral_nonneg_of_forall c.period_pos.le (fun x => sq_nonneg _)
  have n := c.growthResidual_support_cost c.arclengthCentroid 0
  have tot := c.centered_tangent_and_normal_moments
  have a := c.radialTangentSupport_oscillation hs ht
  change (c.energy/2)^2≤r*_ at n
  change Real.pi^2*r*_≤r*c.period^4-Real.pi^2*c.energy^2*c.period
  nlinarith only [mul_le_mul_of_nonneg_left n (show 0≤4*Real.pi^2*c.period by have := c.period_pos; positivity),
    mul_le_mul_of_nonneg_left tot (mul_nonneg hr c.period_pos.le),
    mul_le_mul_of_nonneg_left a (mul_nonneg (sq_nonneg Real.pi) hr)]
end LengthGrowth.ClosedFrenetCurve

#print axioms LengthGrowth.ClosedFrenetCurve.growthResidual_centroid_annulus
