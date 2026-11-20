import LengthGrowth.OscillatorMean
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Algebra.Field.Periodic

noncomputable section
namespace LengthGrowth.OscillatorMean
open Set Real MeasureTheory

theorem periodic_window_error {f : ℝ → ℝ} {p A μ : ℝ}
    (hp : 0<p) (cf : Continuous f) (per : Function.Periodic f p)
    (hA : ∀ t, |f t|≤A) (hmean : (∫ t in 0..p,f t)=p*μ) (s T : ℝ) (hT : 0<T) :
    |(∫ t in s..s+T,f t)/T-μ| ≤ 2*A*p/T := by
  have av := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=0) (b:=p) (C:=A) (f:=f) (fun t _ => by simpa only [Real.norm_eq_abs] using hA t)
  rw [Real.norm_eq_abs,hmean,abs_mul,abs_of_pos hp] at av
  have hm : |μ|≤A := by
    apply le_of_mul_le_mul_left (a:=p) _ hp
    simpa [abs_of_pos hp,mul_comm] using av
  let g : ℝ → ℝ := fun t => f t-μ
  have cg : Continuous g := cf.sub continuous_const
  have pg : Function.Periodic g p := fun t => by change f (t+p)-μ=_; rw [per t]
  have g0 : (∫ t in 0..p,g t)=0 := by
    dsimp only [g]
    rw [intervalIntegral.integral_sub (cf.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _),intervalIntegral.integral_const,hmean]
    simp only [sub_zero,smul_eq_mul,sub_self]
  let R : ℝ → ℝ := fun x => ∫ t in s..s+x,g t
  have pR : Function.Periodic R p := by
    intro x
    dsimp only [R]
    rw [← add_assoc,pg.intervalIntegral_add_eq_add s (s+x) cg.intervalIntegrable,
      pg.intervalIntegral_add_eq s 0,zero_add,g0,add_zero]
  obtain ⟨x,hx,eqx⟩ := pR.exists_mem_Ico₀ hp T
  have ga (t : ℝ) : ‖g t‖≤2*A := by
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by linarith only [hA t,hm])
  have bound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=s) (b:=s+x) (f:=g) (C:=2*A) (fun t _ => ga t)
  rw [Real.norm_eq_abs] at bound
  have bx : |R x|≤2*A*x := by
    simpa [R,abs_of_nonneg hx.1] using bound
  have gain : |R T|≤2*A*p := eqx ▸ bx.trans
    (mul_le_mul_of_nonneg_left hx.2.le (by linarith only [abs_nonneg (f 0),hA 0]))
  have exactR : R T=(∫ t in s..s+T,f t)-T*μ := by
    dsimp only [R,g]
    rw [intervalIntegral.integral_sub (cf.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _),intervalIntegral.integral_const]
    simp only [add_sub_cancel_left,smul_eq_mul]
  rw [show (∫ t in s..s+T,f t)/T-μ=R T/T by rw [exactR]; field_simp [hT.ne'],
    abs_div,abs_of_pos hT]
  exact div_le_div_of_nonneg_right gain hT.le

end LengthGrowth.OscillatorMean
