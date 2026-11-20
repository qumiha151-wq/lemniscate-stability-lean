import LengthGrowth.ActualFlow.ExponentialPosition

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

/-- The expression produced by differentiating the weighted length plus bending
energy in the normal gauge, after integrating both force derivatives by parts. -/
def weightedRateIntegrand (a k j F q n : ℝ) : ℝ :=
  -F^2-F*(a^2*q^2*k+3/2*a*n*k^2+2*a*q*j)+a^2*F*(k-a*n)

theorem weighted_square_bound (a k j F q n : ℝ) (hq : |q|≤1) (hn : |n|≤1) :
    weightedRateIntegrand a k j F q n -
      8*a^2*(a*q*k*j+j^2+k*(F-k^3/2)) ≤ 256*(a^4+a^2*k^2)*(k^2/2+a^2) := by
  have usq {x : ℝ} (hx : |x|≤1) : x^2≤1 := by
    have z := sq_le_sq' (abs_le.mp hx).1 (abs_le.mp hx).2
    exact z.trans_eq (by norm_num)
  have q2 := usq hq
  have n2 := usq hn
  have q4 : q^4≤1 := by nlinarith only [mul_self_le_mul_self (sq_nonneg q) q2]
  unfold weightedRateIntegrand
  nlinarith only [sq_nonneg (F+4*(a^2*q^2*k)),sq_nonneg (F+4*(3/2*a*n*k^2)),
    sq_nonneg (F+4*(7*a^2*k)),sq_nonneg (F+4*(a^3*n)),
    sq_nonneg (F+4*a*q*j),sq_nonneg (2*a*j+2*a^2*q*k),sq_nonneg F,
    mul_le_mul_of_nonneg_right q4 (by positivity : 0≤a^4*k^2),
    mul_le_mul_of_nonneg_right n2 (by positivity : 0≤a^2*k^4),
    mul_le_mul_of_nonneg_right n2 (by positivity : 0≤a^6),
    mul_le_mul_of_nonneg_right q2 (by positivity : 0≤a^2*j^2),
    mul_le_mul_of_nonneg_right q2 (by positivity : 0≤a^4*k^2),
    show 0≤a^4*k^2 by positivity, show 0≤a^2*k^4 by positivity,show 0≤a^6 by positivity]

/-- The weighted spatial rate on the genuine closed unit-speed slice. Its
periodic cross term integrates exactly to zero. -/
theorem exponential_spatial_rate (l : ℂ →L[ℝ] ℝ) (hl : ∀z, |l z| ≤ ‖z‖)
    (a M : ℝ) (hM : ∀s∈Icc 0 c.period, |c.curvature s|≤M) :
    (∫ s in 0..c.period, Real.exp (a*l (c.curve s))*
      weightedRateIntegrand a (c.curvature s) (c.curvature₁ s) (c.force s)
        (l (c.tangent s)) (l (c.normal s))) ≤ 256*(a^4+a^2*M^2)*c.exponentialMass l a := by
  let w := fun s => Real.exp (a*l (c.curve s))
  let v := fun s => w s*weightedRateIntegrand a (c.curvature s) (c.curvature₁ s)
    (c.force s) (l (c.tangent s)) (l (c.normal s))
  let d := fun s => 8*a^2*w s*(a*l (c.tangent s)*c.curvature s*c.curvature₁ s+
    c.curvature₁ s^2+c.curvature s*c.curvature₂ s)
  let e := fun s => w s*(c.curvature s^2/2+a^2)
  let g := fun s => 8*a^2*w s*c.curvature s*c.curvature₁ s
  have cx : Continuous c.curve := continuous_iff_continuousAt.mpr fun x => (c.curve_deriv x).continuousAt
  have cn : Continuous c.normal := continuous_iff_continuousAt.mpr fun x => (c.normal_deriv x).continuousAt
  have cw : Continuous w := ((l.continuous.comp cx).const_mul a).rexp
  have ck := c.curvature_continuous
  have cj := c.curvature₁_continuous
  have cf := c.force_continuous
  have cT := c.tangent_continuous
  have ct := l.continuous.comp c.tangent_continuous
  have cnn := l.continuous.comp cn
  have c2 := c.curvature₂_continuous
  have cv : Continuous v := by dsimp [v,weightedRateIntegrand]; fun_prop
  have cd : Continuous d := by dsimp [d]; fun_prop
  have ce : Continuous e := by dsimp [e]; fun_prop
  have hd (s : ℝ) : HasDerivAt g (d s) s := by
    have hc := l.hasFDerivAt.comp_hasDerivAt s (c.curve_deriv s)
    have hw := (hc.const_mul a).exp
    have hh := (((hw.const_mul (8*a^2)).mul (c.curvature_deriv s)).mul (c.curvature₁_deriv s))
    convert! hh using 1
    dsimp [d,w,Function.comp_def]
    ring
  have gp : g c.period=g 0 := by
    have hx := c.curve_periodic 0
    have hk := c.curvature_periodic 0
    have hj := c.curvature₁_periodic 0
    simp only [zero_add] at hx hk hj
    simp only [g,w,hx,hk,hj]
  have dz := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=c.period)
    (fun s _ => hd s) (cd.intervalIntegrable _ _)
  rw [gp,sub_self] at dz
  have est (s : ℝ) (hs : s∈Icc 0 c.period) : v s-d s≤256*(a^4+a^2*M^2)*e s := by
    have iq := weighted_square_bound a (c.curvature s) (c.curvature₁ s) (c.force s)
      (l (c.tangent s)) (l (c.normal s)) ((hl _).trans_eq (c.tangent_unit s))
      ((hl _).trans_eq (c.normal_unit s))
    have ik : c.curvature s^2≤M^2 := sq_le_sq' (abs_le.mp (hM s hs)).1 (abs_le.mp (hM s hs)).2
    have hj : c.force s-c.curvature s^3/2=c.curvature₂ s := by simp [force]
    rw [hj] at iq
    have leC : a^4+a^2*c.curvature s^2≤a^4+a^2*M^2 := by gcongr
    have enk : 0≤c.curvature s^2/2+a^2 := by positivity
    have iC := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left leC (by norm_num : (0:ℝ)≤256)) enk
    have final := mul_le_mul_of_nonneg_left (iq.trans iC) (show 0≤w s from (Real.exp_pos _).le)
    dsimp only [v,d,e]
    linarith only [final]
  have iw := intervalIntegral.integral_mono_on (μ:=volume) c.period_pos.le
    ((cv.sub cd).intervalIntegrable _ _) ((ce.const_mul (256*(a^4+a^2*M^2))).intervalIntegrable _ _) est
  simp only [Pi.sub_apply] at iw
  rw [intervalIntegral.integral_sub (cv.intervalIntegrable _ _) (cd.intervalIntegrable _ _),
    dz,sub_zero,intervalIntegral.integral_const_mul] at iw
  exact iw

end LengthGrowth.ClosedFrenetCurve
#print axioms LengthGrowth.ClosedFrenetCurve.exponential_spatial_rate
