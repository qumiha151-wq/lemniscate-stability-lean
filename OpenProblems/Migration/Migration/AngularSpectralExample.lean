import Migration.AngularReconstruction

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.AngularGauge.Example

def angle (x : ℝ) := x + Real.sin (2*x)/10
def v (x : ℝ) := 1 + Real.cos (2*x)/5
def w (x : ℝ) := -(2/5 : ℝ)*Real.sin (2*x)
def f (x : ℝ) := -(4/5 : ℝ)*Real.cos (2*x)+(v x)^3/2
def B (y : ℝ) := -(77/375 : ℝ)-(1403/20000 : ℝ)*y-y^2/375-y^3/10000
def BP (y : ℝ) := -(1403/20000 : ℝ)-2*y/375-3*y^2/10000
def primitive (x : ℝ) := Real.sin (2*x)*B (Real.cos (2*x))
def u (x : ℝ) := -v x*w x+primitive x
def fx (x : ℝ) := (8/5 : ℝ)*Real.sin (2*x)+(3/2 : ℝ)*(v x)^2*w x
def pol (y : ℝ) := -(8/5 : ℝ)+(1+y/5)^2+(1+y/5)*B y
def firstVelocity (x : ℝ) := Real.sin (2*x)*pol (Real.cos (2*x))

private theorem arg_der (x : ℝ) : HasDerivAt (fun z : ℝ => 2*z) (2:ℝ) x := by
  simpa using (hasDerivAt_id x).const_mul 2

theorem geometry (x : ℝ) : HasDerivAt angle (v x) x ∧
    HasDerivAt v (w x) x ∧ HasDerivAt w (f x-(v x)^3/2) x ∧
    HasDerivAt f (fx x) x := by
  have cs := (arg_der x).cos
  have sn := (arg_der x).sin
  have d : HasDerivAt v (w x) x := by
    apply ((cs.div_const 5).const_add 1).congr_deriv
    dsimp only [w]; ring
  refine ⟨?_,d,?_,?_⟩
  · apply ((hasDerivAt_id x).add (sn.div_const 10)).congr_deriv
    dsimp only [v]; ring
  · apply (sn.const_mul (-(2/5 : ℝ))).congr_deriv
    dsimp only [f]; ring
  · apply ((cs.const_mul (-(4/5 : ℝ))).add ((d.pow 3).div_const 2)).congr_deriv
    dsimp only [fx]; ring

private theorem B_der (y : ℝ) : HasDerivAt B (BP y) y := by
  have dy := hasDerivAt_id y
  apply (((((dy.const_mul (1403/20000 : ℝ)).const_sub (-(77/375 : ℝ))).sub
    ((dy.pow 2).div_const 375)).sub ((dy.pow 3).div_const 10000))).congr_deriv
  dsimp [BP]; ring

theorem primitive_der (x : ℝ) : HasDerivAt primitive
    ((w x)^2-(v x)^4/2+4803/10000) x := by
  apply (((arg_der x).sin).mul ((B_der _).comp x (arg_der x).cos)).congr_deriv
  dsimp [B,BP,w,v]
  linear_combination (norm := (dsimp [BP]; ring)) (-2*BP (Real.cos (2*x))-4/25)*(Real.sin_sq_add_cos_sq (2*x))

theorem gauge (x : ℝ) : HasDerivAt u ((4803/10000 : ℝ)-v x*f x) x ∧
    firstVelocity x= -fx x + u x*v x := by
  obtain ⟨_,d,e,_⟩ := geometry x
  constructor
  · apply ((d.neg.mul e).add (primitive_der x)).congr_deriv
    simp only [Pi.neg_apply]; ring
  · unfold firstVelocity pol fx u primitive v w
    ring

theorem nonconstant_force : f 0 ≠ f (Real.pi/4) := by
  norm_num [f,v,show (2:ℝ)*(Real.pi/4)=Real.pi/2 by ring]

theorem half_turn (x : ℝ) : angle (x+Real.pi)=angle x+Real.pi := by
  unfold angle
  rw [show 2*(x+Real.pi)=2*x+2*Real.pi by ring,Real.sin_add_two_pi]
  ring

/-- The initial horizontal and vertical displacements vanish exactly. -/
theorem closed_projection (a b : ℝ) :
    (∫x in (0:ℝ)..(2*Real.pi),a*Real.cos (angle x)+b*Real.sin (angle x))=0 := by
  let z := fun x => a*Real.cos (angle x)+b*Real.sin (angle x)
  have ct : Continuous angle := continuous_iff_continuousAt.mpr fun x => (geometry x).1.continuousAt
  have cz : Continuous z := (continuous_const.mul (Real.continuous_cos.comp ct)).add
    (continuous_const.mul (Real.continuous_sin.comp ct))
  have anti (x : ℝ) : z (x+Real.pi)= -z x := by
    dsimp only [z]; rw [half_turn,Real.cos_add_pi,Real.sin_add_pi]; ring
  have shift := intervalIntegral.integral_comp_add_right z Real.pi (a:=0) (b:=Real.pi)
  simp only [anti,zero_add,intervalIntegral.integral_neg] at shift
  change (∫ x in (0:ℝ)..(2*Real.pi),z x)=0
  rw [show (2:ℝ)*Real.pi=Real.pi+Real.pi by ring,
    ← intervalIntegral.integral_add_adjacent_intervals (cz.intervalIntegrable (μ:=volume) 0 Real.pi)
      (cz.intervalIntegrable (μ:=volume) Real.pi (Real.pi+Real.pi)),← shift]
  ring

/-- A single Fourier mode of the biharmonic heat operator satisfies the
singular smoothing bound used to pass from an unweighted residual to X.
The sharper exp maximum is unnecessary here. -/
theorem smoothing_mode {s n : ℝ} (sp : 0<s) :
    (1+n^2)*Real.exp (-s*n^4) ≤ 1+1/Real.sqrt (2*s) := by
  have e := Real.add_one_le_exp (2*(s*n^4))
  have ep := Real.exp_pos (-s*n^4)
  have fac : (Real.exp (-s*n^4))^2*Real.exp (2*(s*n^4))=1 := by
    rw [pow_two,← Real.exp_add,← Real.exp_add,show -s*n^4+-s*n^4+2*(s*n^4)=0 by ring,Real.exp_zero]
  have bound := mul_le_mul_of_nonneg_left e (sq_nonneg (Real.exp (-s*n^4)))
  have rad := Real.sq_sqrt (show 0≤2*s by positivity)
  have hp : 0<Real.sqrt (2*s) := Real.sqrt_pos.2 (by positivity)
  have s2 : (Real.sqrt (2*s)*(n^2*Real.exp (-s*n^4)))^2≤1 := by
    rw [mul_pow,rad,mul_pow]; nlinarith only [bound,fac,sq_nonneg (Real.exp (-s*n^4))]
  have single : n^2*Real.exp (-s*n^4)≤1/Real.sqrt (2*s) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith only [s2,sq_nonneg (Real.sqrt (2*s)*(n^2*Real.exp (-s*n^4))-1)]
  have ee : Real.exp (-s*n^4)≤1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg sp.le (sq_nonneg (n^2))])
  linarith only [ee,single]

end MigrationGeometry.AngularGauge.Example
#print axioms MigrationGeometry.AngularGauge.Example.gauge
#print axioms MigrationGeometry.AngularGauge.Example.closed_projection
#print axioms MigrationGeometry.AngularGauge.Example.smoothing_mode
