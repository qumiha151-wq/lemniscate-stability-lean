import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Residual stability of the forced quartic oscillator on a finite interval. -/
noncomputable section
namespace LengthGrowth.QuarticStability
open Real Set MeasureTheory

def force (z : ℝ) := -z^3/2+z/4+1/4

def energy (z d h : ℝ) :=
  h^2/2 + d^2*((d+2*z)^2/8+z^2/4+1/2)

theorem position_sq_le (z d h : ℝ) : d^2 ≤ 2*energy z d h := by
  unfold energy
  nlinarith only [sq_nonneg h, mul_nonneg (sq_nonneg d) (sq_nonneg (d+2*z)),
    mul_nonneg (sq_nonneg d) (sq_nonneg z)]

private theorem rate_bound (z d h q w V : ℝ) (hq : |q|≤V) :
    h*w+(5/4)*d*h+q*(d^2*(d+3*z)/2) ≤ (3+2*V)*energy z d h+w^2/2 := by
  let H := energy z d h
  have hpos : d^2/2+h^2/2 ≤ H := by
    dsimp [H,energy]
    nlinarith only [mul_nonneg (sq_nonneg d) (sq_nonneg (d+2*z)),
      mul_nonneg (sq_nonneg d) (sq_nonneg z)]
  have hn : 0≤H := by linarith only [hpos,sq_nonneg d,sq_nonneg h]
  have ha : |d^2*(d+3*z)/2| ≤ 2*H := by
    apply abs_le.mpr
    dsimp [H,energy]
    constructor
    · nlinarith only [sq_nonneg h,sq_nonneg d,
        mul_nonneg (sq_nonneg d) (sq_nonneg (d+2*z+1)),
        mul_nonneg (sq_nonneg d) (sq_nonneg (z+1/2))]
    · nlinarith only [sq_nonneg h,sq_nonneg d,
        mul_nonneg (sq_nonneg d) (sq_nonneg (d+2*z-1)),
        mul_nonneg (sq_nonneg d) (sq_nonneg (z-1/2))]
  have hq' : q*(d^2*(d+3*z)/2) ≤ V*(2*H) := by
    calc
      _ ≤ |q*(d^2*(d+3*z)/2)| := le_abs_self _
      _ = _ := abs_mul _ _
      _ ≤ _ := mul_le_mul hq ha (abs_nonneg _) ((abs_nonneg q).trans hq)
  change _ ≤ (3+2*V)*H+w^2/2
  nlinarith only [hq',hpos,sq_nonneg (d-h),sq_nonneg (w-h),sq_nonneg d,hn]

/-- The reference solution has bounded speed on the comparison interval.
The forced solution only needs a bound on the integral of its squared residual. -/
theorem comparison {u p z q w : ℝ → ℝ} {x t V : ℝ}
    (hxt : x≤t) (cw : Continuous w)
    (du : ∀ s, HasDerivAt u (p s) s) (dp : ∀ s, HasDerivAt p (force (u s)+w s) s)
    (dz : ∀ s, HasDerivAt z (q s) s) (dq : ∀ s, HasDerivAt q (force (z s)) s)
    (pos0 : u x=z x) (vel0 : p x=q x) (speed : ∀ s ∈ Icc x t, |q s|≤V) :
    (u t-z t)^2 ≤ exp ((3+2*V)*(t-x)) * ∫ s in x..t, (w s)^2 := by
  let d := u-z
  let h := p-q
  let H := fun s => energy (z s) (d s) (h s)
  let rate := fun s => h s*w s+(5/4)*d s*h s+q s*((d s)^2*(d s+3*z s)/2)
  let k := 3+2*V
  let g := fun s => exp (-(k*(s-x)))
  have cd : Continuous d := continuous_iff_continuousAt.mpr
    (fun s => ((du s).sub (dz s)).continuousAt)
  have ch : Continuous h := continuous_iff_continuousAt.mpr
    (fun s => ((dp s).sub (dq s)).continuousAt)
  have cz : Continuous z := continuous_iff_continuousAt.mpr (fun s => (dz s).continuousAt)
  have cq : Continuous q := continuous_iff_continuousAt.mpr (fun s => (dq s).continuousAt)
  have cH : Continuous H := by dsimp [H,energy]; fun_prop
  have cR : Continuous rate := by dsimp [rate]; fun_prop
  have cg : Continuous g := by dsimp [g]; fun_prop
  have dH (s : ℝ) : HasDerivAt H (rate s) s := by
    have dd : HasDerivAt d (h s) s := (du s).sub (dz s)
    have dh : HasDerivAt h (force (u s)+w s-force (z s)) s := (dp s).sub (dq s)
    have factor := ((((dd.add ((dz s).const_mul 2)).pow 2).div_const 8).add
      (((dz s).pow 2).div_const 4)).add_const (1/2)
    have deriv := (((dh.pow 2).div_const 2).add ((dd.pow 2).mul factor))
    convert deriv using 1 <;> first | rfl | (simp only [rate,h,d,force,Pi.sub_apply,Pi.pow_apply,Pi.add_apply]; ring)
  let integrand := fun s => g s*(rate s-k*H s)
  have ci : Continuous integrand := cg.mul (cR.sub (cH.const_mul k))
  have dweighted (s : ℝ) : HasDerivAt (fun y => g y*H y) (integrand s) s := by
    have dg := (((((hasDerivAt_id s).sub_const x).const_mul k).neg.exp).mul (dH s))
    convert dg using 1 <;> first | rfl | (simp only [integrand,g,id_eq,Pi.neg_apply]; ring)
  have hk : 0≤k := by
    have := (abs_nonneg (q x)).trans (speed x ⟨le_rfl,hxt⟩)
    dsimp [k]; linarith
  have pointwise (s) (hs : s ∈ Icc x t) : integrand s ≤ (1/2)*(w s)^2 := by
    have hr := rate_bound (z s) (d s) (h s) (q s) (w s) V (speed s hs)
    have hr' : rate s-k*H s ≤ (1/2)*(w s)^2 := by
      dsimp [rate,k,H]; linarith only [hr]
    have gpos : 0≤g s := (exp_pos _).le
    have gone : g s ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hk (sub_nonneg.mpr hs.1)))
    exact (mul_le_mul_of_nonneg_left hr' gpos).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right gone (show 0≤(1/2:ℝ)*(w s)^2 by positivity))
  have hh := intervalIntegral.integral_mono_on (μ:=volume) hxt (ci.intervalIntegrable _ _)
    (((cw.pow 2).const_mul (1/2)).intervalIntegrable _ _) pointwise
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => dweighted s)
    (ci.intervalIntegrable x t),intervalIntegral.integral_const_mul] at hh
  have hx : H x=0 := by simp [H,d,h,energy,pos0,vel0]
  rw [hx,mul_zero,sub_zero] at hh
  change exp (-(k*(t-x))) * H t ≤ _ at hh
  rw [exp_neg,←div_eq_inv_mul] at hh
  have hmul := (div_le_iff₀ (exp_pos (k*(t-x)))).mp hh
  have hpoint : (u t-z t)^2 ≤ 2*H t := position_sq_le _ _ _
  change (u t-z t)^2 ≤ exp (k*(t-x))*(∫ y in x..t,(w^2) y)
  nlinarith only [hpoint,hmul]

/-- Small integrated squared residual gives uniform position control on the whole window. -/
theorem window_bound {u p z q w : ℝ → ℝ} {x T V K η : ℝ}
    (hT : 1≤T) (hη : 0≤η) (hK : 3+2*V≤2*K) (cw : Continuous w)
    (du : ∀ s, HasDerivAt u (p s) s) (dp : ∀ s, HasDerivAt p (force (u s)+w s) s)
    (dz : ∀ s, HasDerivAt z (q s) s) (dq : ∀ s, HasDerivAt q (force (z s)) s)
    (pos0 : u x=z x) (vel0 : p x=q x) (speed : ∀ s ∈ Icc x (x+T), |q s|≤V)
    (small : (∫ s in x..x+T,(w s)^2) ≤ (η*exp (-(K*T)))^2/T) :
    ∀ t ∈ Icc x (x+T), |u t-z t| ≤ η := by
  intro t ht
  have vpos : 0≤V := (abs_nonneg (q t)).trans (speed t ht)
  have htime : 0≤T := by linarith
  have hrate : (3+2*V)*(t-x) ≤ 2*(K*T) := by
    calc
      _ ≤ (3+2*V)*T := mul_le_mul_of_nonneg_left (by linarith only [ht.2]) (by linarith)
      _ ≤ (2*K)*T := mul_le_mul_of_nonneg_right hK htime
      _ = _ := by ring
  have iw := (cw.pow 2).intervalIntegrable (μ:=volume) x (x+T)
  have hprefix : (∫ y in x..t,(w y)^2) ≤ ∫ y in x..x+T,(w y)^2 :=
    intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Filter.Eventually.of_forall fun y => sq_nonneg (w y)) iw
  have hsmall : (∫ s in x..t,(w s)^2) ≤ (η*exp (-(K*T)))^2 := by
    apply (hprefix.trans small).trans
    exact div_le_self (sq_nonneg _) hT
  have h := comparison ht.1 cw du dp dz dq pos0 vel0
    (fun s hs => speed s ⟨hs.1,hs.2.trans ht.2⟩)
  have hi : 0≤∫ s in x..t,(w s)^2 :=
    intervalIntegral.integral_nonneg_of_forall ht.1 fun s => sq_nonneg _
  have hbound := mul_le_mul (exp_le_exp.mpr hrate) hsmall hi (exp_pos _).le
  have hc : exp (2*(K*T))*(η*exp (-(K*T)))^2=η^2 := by
    rw [two_mul,exp_add,exp_neg]
    field_simp
  rw [hc] at hbound
  exact abs_le_of_sq_le_sq (h.trans hbound) hη

#print axioms comparison
#print axioms window_bound

end LengthGrowth.QuarticStability
