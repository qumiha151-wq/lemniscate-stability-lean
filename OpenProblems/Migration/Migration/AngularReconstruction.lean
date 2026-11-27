import Migration.CurveKinematics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.AngularGauge

/-- The equiarclength angle equation on an open normalized time interval.
The spatial derivatives determine the scaled elastic force f. -/
structure Chart (I : Set ℝ) (P : ℝ) where
  openTime : IsOpen I
  rho : ℝ → ℝ
  theta : ℝ → ℝ → ℝ
  v : ℝ → ℝ → ℝ
  w : ℝ → ℝ → ℝ
  f : ℝ → ℝ → ℝ
  fx : ℝ → ℝ → ℝ
  u : ℝ → ℝ → ℝ
  A : ℝ → ℝ
  winding : ℤ
  rho_pos : ∀t∈I,0<rho t
  rho_cont : ContinuousOn rho I
  angle_cont : ContinuousOn (fun z : ℝ × ℝ => theta z.1 z.2) (I ×ˢ univ)
  v_cont : ContinuousOn (fun z : ℝ × ℝ => v z.1 z.2) (I ×ˢ univ)
  u_cont : ContinuousOn (fun z : ℝ × ℝ => u z.1 z.2) (I ×ˢ univ)
  fx_cont : ContinuousOn (fun z : ℝ × ℝ => fx z.1 z.2) (I ×ˢ univ)
  A_cont : ContinuousOn A I
  theta_x : ∀t∈I,∀x, HasDerivAt (theta t) (v t x) x
  v_x : ∀t∈I,∀x, HasDerivAt (v t) (w t x) x
  w_x : ∀t∈I,∀x, HasDerivAt (w t) (f t x-(v t x)^3/2) x
  force_x : ∀t∈I,∀x, HasDerivAt (f t) (fx t x) x
  u_x : ∀t∈I,∀x, HasDerivAt (u t) (A t-v t x*f t x) x
  theta_t : ∀t∈I,∀x, HasDerivAt (fun z => theta z x) (-fx t x+u t x*v t x) t
  rho_t : ∀t∈I, HasDerivAt rho (rho t*A t) t
  twist : ∀t∈I,∀x,theta t (x+P)=theta t x+winding*(2*Real.pi)
  perV : ∀t∈I,Function.Periodic (v t) P
  perW : ∀t∈I,Function.Periodic (w t) P
  perF : ∀t∈I,Function.Periodic (f t) P
  perU : ∀t∈I,Function.Periodic (u t) P

namespace Chart
variable {I : Set ℝ} {P : ℝ} (c : Chart I P)

def T (a b t x : ℝ) := a*Real.cos (c.theta t x)+b*Real.sin (c.theta t x)
def N (a b t x : ℝ) := -a*Real.sin (c.theta t x)+b*Real.cos (c.theta t x)
def slope (a b t x : ℝ) := c.rho t*c.T a b t x
def velocity (a b t x : ℝ) := c.rho t*(c.u t x*c.T a b t x-c.f t x*c.N a b t x)
def mixed (a b t x : ℝ) := c.rho t*(c.A t*c.T a b t x+(-c.fx t x+c.u t x*c.v t x)*c.N a b t x)
def position (a b : ℝ) (anchor : ℝ → ℝ) (t x : ℝ) := anchor t+∫s in (0:ℝ)..x,c.slope a b t s
def periodShift (a b t : ℝ) := ∫s in (0:ℝ)..P,c.slope a b t s

private theorem t_der {g : ℝ → ℝ} {s m : ℝ} (hg : HasDerivAt g m s) (a b : ℝ) :
    HasDerivAt (fun x=>a*Real.cos (g x)+b*Real.sin (g x)) (m*(-a*Real.sin (g s)+b*Real.cos (g s))) s := by
  apply (((hg.cos).const_mul a).add ((hg.sin).const_mul b)).congr_deriv; ring

private theorem n_der {g : ℝ → ℝ} {s m : ℝ} (hg : HasDerivAt g m s) (a b : ℝ) :
    HasDerivAt (fun x=> -a*Real.sin (g x)+b*Real.cos (g x)) (-m*(a*Real.cos (g s)+b*Real.sin (g s))) s := by
  apply (((hg.sin).const_mul (-a)).add ((hg.cos).const_mul b)).congr_deriv; ring

theorem slope_time {t : ℝ} (ht : t∈I) (a b x : ℝ) :
    HasDerivAt (fun s=>c.slope a b s x) (c.mixed a b t x) t := by
  apply ((c.rho_t t ht).mul (t_der (c.theta_t t ht x) a b)).congr_deriv
  dsimp only [T,N,mixed]; ring

theorem velocity_space {t : ℝ} (ht : t∈I) (a b x : ℝ) :
    HasDerivAt (c.velocity a b t) (c.mixed a b t x) x := by
  apply ((((c.u_x t ht x).mul (t_der (c.theta_x t ht x) a b)).sub
    ((c.force_x t ht x).mul (n_der (c.theta_x t ht x) a b))).const_mul (c.rho t)).congr_deriv
  dsimp only [mixed,T,N]; ring

private theorem conts (a b : ℝ) :
    ContinuousOn (fun z : ℝ × ℝ => c.slope a b z.1 z.2) (I ×ˢ univ) ∧
    ContinuousOn (fun z : ℝ × ℝ => c.mixed a b z.1 z.2) (I ×ˢ univ) := by
  have rh : ContinuousOn (fun z : ℝ × ℝ => c.rho z.1) (I ×ˢ univ) :=
    c.rho_cont.comp continuous_fst.continuousOn (fun _ h => h.1)
  have ca : ContinuousOn (fun z : ℝ × ℝ => c.A z.1) (I ×ˢ univ) :=
    c.A_cont.comp continuous_fst.continuousOn (fun _ h => h.1)
  have ct : ContinuousOn (fun z : ℝ × ℝ => c.T a b z.1 z.2) (I ×ˢ univ) :=
    (continuousOn_const.mul (Real.continuous_cos.comp_continuousOn c.angle_cont)).add
      (continuousOn_const.mul (Real.continuous_sin.comp_continuousOn c.angle_cont))
  have cn : ContinuousOn (fun z : ℝ × ℝ => c.N a b z.1 z.2) (I ×ˢ univ) :=
    (continuousOn_const.mul (Real.continuous_sin.comp_continuousOn c.angle_cont)).add
      (continuousOn_const.mul (Real.continuous_cos.comp_continuousOn c.angle_cont))
  exact ⟨rh.mul ct,rh.mul ((ca.mul ct).add ((c.fx_cont.neg.add (c.u_cont.mul c.v_cont)).mul cn))⟩

private theorem slice {F : ℝ → ℝ → ℝ} {t : ℝ} (ht : t∈I)
    (hf : ContinuousOn (fun z : ℝ × ℝ => F z.1 z.2) (I ×ˢ univ)) : Continuous (F t) :=
  continuousOn_univ.mp (hf.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ _ => ⟨ht,mem_univ _⟩))

theorem primitive_time {t : ℝ} (ht : t∈I) (a b x : ℝ) :
    HasDerivAt (fun z=>∫s in (0:ℝ)..x,c.slope a b z s) (c.velocity a b t x-c.velocity a b t 0) t := by
  obtain ⟨cs,cm⟩ := c.conts a b
  have sub : I ×ˢ uIcc 0 x ⊆ I ×ˢ (univ : Set ℝ) := fun _ h => ⟨h.1,mem_univ _⟩
  have res := Flow.hasDerivAt_intervalIntegral_of_continuousOn c.openTime (cs.mono sub) (cm.mono sub)
    (fun z hz s _ => c.slope_time hz a b s) ht
  have cmx : Continuous (c.mixed a b t) := slice ht cm
  rwa [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => c.velocity_space ht a b s)
    (cmx.intervalIntegrable ..)] at res

theorem periodicTN {t : ℝ} (ht : t∈I) (a b : ℝ) :
    Function.Periodic (c.T a b t) P ∧ Function.Periodic (c.N a b t) P := by
  constructor <;> intro x <;> simp only [T,N,c.twist t ht x,Real.cos_add_int_mul_two_pi,Real.sin_add_int_mul_two_pi]

theorem periodicVelocity {t : ℝ} (ht : t∈I) (a b : ℝ) : Function.Periodic (c.velocity a b t) P := by
  intro x
  simp only [velocity,c.perU t ht x,c.perF t ht x,(c.periodicTN ht a b).1 x,(c.periodicTN ht a b).2 x]

/-- Horizontal and vertical displacement over a parameter period are
conserved by the actual angle equation. -/
theorem periodShift_derivative {t : ℝ} (ht : t∈I) (a b : ℝ) :
    HasDerivAt (c.periodShift a b) 0 t := by
  have h := c.periodicVelocity ht a b 0
  simp only [zero_add] at h
  change HasDerivAt (fun z=>∫s in (0:ℝ)..P,c.slope a b z s) 0 t
  simpa only [h,sub_self] using c.primitive_time ht a b P

theorem periodShift_constant {t₀ t₁ : ℝ} (le : t₀≤t₁) (int : Icc t₀ t₁ ⊆ I) (a b : ℝ) :
    c.periodShift a b t₁=c.periodShift a b t₀ := by
  have d (s : ℝ) (hs : s∈Icc t₀ t₁) := c.periodShift_derivative (int hs) a b
  have ft := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=t₀) (b:=t₁)
    (fun s hs => d s (by rwa [uIcc_of_le le] at hs)) ((continuous_const : Continuous (fun _ : ℝ => (0:ℝ))).intervalIntegrable ..)
  simp only [intervalIntegral.integral_zero] at ft
  exact sub_eq_zero.mp ft.symm

theorem position_time {t : ℝ} (ht : t∈I) (a b x : ℝ) (anchor : ℝ→ℝ)
    (anch : HasDerivAt anchor (c.velocity a b t 0) t) :
    HasDerivAt (fun s=>c.position a b anchor s x) (c.velocity a b t x) t := by
  apply (anch.add (c.primitive_time ht a b x)).congr_deriv
  ring

theorem position_space {t : ℝ} (ht : t∈I) (a b x : ℝ) (anchor : ℝ→ℝ) :
    HasDerivAt (c.position a b anchor t) (c.slope a b t x) x := by
  have cs : Continuous (c.slope a b t) := slice ht (c.conts a b).1
  exact ((intervalIntegral.integral_hasDerivAt_right (cs.intervalIntegrable ..)
    (cs.stronglyMeasurableAtFilter _ _) cs.continuousAt).const_add _)

/-- Normal force has zero vector mean in both projections. This removes
the third spatial derivative from the drift needed to reconstruct position. -/
theorem mean_normal_velocity_zero {t : ℝ} (ht : t∈I) (a b : ℝ) :
    (∫s in (0:ℝ)..P,c.f t s*c.N a b t s)=0 := by
  let H := fun s=> ((c.v t s)^2/2)*c.T a b t s+c.w t s*c.N a b t s
  have hor (s) : HasDerivAt H (c.f t s*c.N a b t s) s := by
    apply (((((c.v_x t ht s).pow 2).div_const 2).mul (t_der (c.theta_x t ht s) a b)).add
      ((c.w_x t ht s).mul (n_der (c.theta_x t ht s) a b))).congr_deriv
    dsimp only [N,T,Pi.pow_apply]; ring
  have hf : Continuous (c.f t) := continuous_iff_continuousAt.mpr fun s => (c.force_x t ht s).continuousAt
  have cn : Continuous (c.N a b t) := continuous_iff_continuousAt.mpr fun s => (n_der (c.theta_x t ht s) a b).continuousAt
  have per : Function.Periodic H P := by
    intro s; simp only [H,c.perV t ht s,c.perW t ht s,(c.periodicTN ht a b).1 s,(c.periodicTN ht a b).2 s]
  have endp := per 0
  simp only [zero_add] at endp
  simpa only [endp,sub_self] using intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=P)
    (fun s _ => hor s) ((hf.mul cn).intervalIntegrable ..)

end Chart
end MigrationGeometry.AngularGauge
#print axioms MigrationGeometry.AngularGauge.Chart.position_time
#print axioms MigrationGeometry.AngularGauge.Chart.periodShift_constant
#print axioms MigrationGeometry.AngularGauge.Chart.mean_normal_velocity_zero
