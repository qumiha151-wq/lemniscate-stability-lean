import Migration.LowDefectVirial
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.MultiDisk

/-- The centered periodic primitive kernel has squared norm 1/12. -/
theorem unit_period_point_bound {f g : ℝ → ℂ}
    (pf : Function.Periodic f 1) (pg : Function.Periodic g 1)
    (df : ∀ s, HasDerivAt f (g s) s) (cg : Continuous g)
    (mean : (∫ s in (0:ℝ)..1, f s) = 0) (a : ℝ) :
    ‖f a‖ ≤ Real.sqrt (1/12) * Real.sqrt (∫ s in (0:ℝ)..1, ‖g s‖^2) := by
  let w := fun s : ℝ => s-a-1/2
  have dw (s : ℝ) : HasDerivAt w 1 s := ((hasDerivAt_id s).sub_const a).sub_const _
  have cw : Continuous w := (continuous_id.sub continuous_const).sub continuous_const
  have cf : Continuous f := continuous_iff_continuousAt.mpr fun s => (df s).continuousAt
  have db (s : ℝ) : HasDerivAt (fun v => w v • f v) (f s+w s • g s) s := by
    have d := (dw s).smul (df s)
    change HasDerivAt (fun v => w v • f v) _ s at d
    simpa only [one_smul,add_comm] using d
  have ft := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=a) (b:=a+1)
    (fun s _ => db s) ((cf.add (cw.smul cg)).intervalIntegrable ..)
  have m : (∫ s in a..a+1, f s) = 0 := by
    simpa only [zero_add,mean] using pf.intervalIntegral_add_eq a 0
  have wa : w a = -(1/2) := by dsimp [w]; ring
  have wb : w (a+1) = 1/2 := by dsimp [w]; ring
  rw [intervalIntegral.integral_add (f:=f) (g:=fun s => w s • g s)
    (cf.intervalIntegrable ..) ((cw.smul cg).intervalIntegrable ..),
    m,zero_add,pf a,wa,wb,←sub_smul,show (1/2:ℝ)- -(1/2)=1 by norm_num,one_smul] at ft
  have hab : a ≤ a+1 := by linarith
  have est := intervalIntegral.norm_integral_le_integral_norm (μ:=volume) (f:=fun s => w s • g s) hab
  rw [ft] at est
  have cs := Flow.interval_integral_abs_mul_le cw cg.norm hab
  have eqn (s : ℝ) : ‖w s • g s‖=|w s*‖g s‖| := by rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (norm_nonneg _)]
  simp only [eqn] at est
  have dp (s : ℝ) : HasDerivAt (fun u => (w u)^3/3) (w s ^ 2) s := by
    apply (((dw s).pow 3).div_const 3).congr_deriv
    ring
  have iw := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=a) (b:=a+1)
    (fun s _ => dp s) ((cw.pow 2).intervalIntegrable ..)
  rw [wb,wa] at iw
  norm_num at iw
  have per : Function.Periodic (fun s => ‖g s‖^2) 1 := fun s => congrArg (fun z : ℂ => ‖z‖^2) (pg s)
  have power := per.intervalIntegral_add_eq a 0
  simp only [zero_add] at power
  rw [iw,power] at cs
  exact est.trans cs

theorem unit_period_scaled_point_bound {f g : ℝ → ℂ} {x : ℝ} (hx : 0≤x)
    (pf : Function.Periodic f 1) (pg : Function.Periodic g 1)
    (df : ∀ s, HasDerivAt f (g s) s) (cg : Continuous g)
    (mean : (∫ s in (0:ℝ)..1, f s)=0)
    (mass : (∫ s in (0:ℝ)..1, ‖g s‖^2) ≤ (2*Real.pi*x)^2) (a : ℝ) :
    ‖f a‖ ≤ (91/50)*x := by
  have q := Real.sqrt_le_sqrt mass
  rw [Real.sqrt_sq (by positivity)] at q
  have h := (unit_period_point_bound pf pg df cg mean a).trans
    (mul_le_mul_of_nonneg_left q (Real.sqrt_nonneg _))
  have sq := Real.sq_sqrt (by norm_num : 0≤(1/12:ℝ))
  have small : Real.sqrt (1/12) ≤ (289/1000:ℝ) := by
    by_contra! bad
    nlinarith only [sq,mul_self_lt_mul_self (by norm_num : (0:ℝ)≤289/1000) bad]
  have pi := Real.pi_lt_d4
  have w := mul_le_mul small pi.le (by positivity : 0≤Real.pi) (by norm_num : (0:ℝ)≤289/1000)
  have v : Real.sqrt (1/12)*(2*Real.pi)≤91/50 := by nlinarith only [w]
  exact h.trans (by simpa only [←mul_assoc] using mul_le_mul_of_nonneg_right v hx)

end MigrationGeometry.MultiDisk
#print axioms MigrationGeometry.MultiDisk.unit_period_scaled_point_bound

