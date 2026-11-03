import Lemniscate.BernoulliGeometry
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! The explicit lemniscate satisfies the normalized free-elastic expander
equation with c=15/2. Arclength differentiation is defined using the actual
speed of the parametrized curve; no elliptic-function identity is needed. -/
namespace Lemniscate
open Complex
open scoped ComplexConjugate ContDiff

noncomputable def arclengthDerivative (γ : ℝ → ℂ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  deriv f u / ‖deriv γ u‖

noncomputable def planarSignedCurvature (γ : ℝ → ℂ) (u : ℝ) : ℝ :=
  (conj (deriv γ u)*deriv (deriv γ) u).im / ‖deriv γ u‖^3

noncomputable def planarNormalSupport (γ : ℝ → ℂ) (u : ℝ) : ℝ :=
  -(conj (γ u)*deriv γ u).im / ‖deriv γ u‖

noncomputable def bernoulliProfileQ (u : ℝ) : ℝ :=
  Real.cos u/Real.sqrt (1+(Real.sin u)^2)

noncomputable def bernoulliProfileP (u : ℝ) : ℝ :=
  -Real.sqrt 2*Real.sin u/(1+(Real.sin u)^2)

theorem bernoulli_profile_data (u : ℝ) :
    HasDerivAt bernoulliProfileQ
      ((Real.sqrt 2*‖bernoulliVelocity u‖)*bernoulliProfileP u) u ∧
    HasDerivAt bernoulliProfileP
      (-(Real.sqrt 2*‖bernoulliVelocity u‖)*(bernoulliProfileQ u)^3) u ∧
    2*(bernoulliProfileP u)^2+(bernoulliProfileQ u)^4 = 1 := by
  let s := Real.sin u
  let c := Real.cos u
  let d := 1+s^2
  let r := Real.sqrt d
  have hd : 0 < d := by dsimp only [d]; nlinarith only [sq_nonneg s]
  have hd0 := ne_of_gt hd
  have hr0 : r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd)
  have hr2 : r^2 = d := Real.sq_sqrt hd.le
  have hr4 : r^4 = d^2 := by rw [show r^4 = (r^2)^2 by ring,hr2]
  have hc2 : c^2 = 1-s^2 := by
    dsimp only [s,c]
    nlinarith only [Real.sin_sq_add_cos_sq u]
  have hc3 : c^3 = c*(1-s^2) := by rw [show c^3 = c*c^2 by ring,hc2]
  have hc4 : c^4 = (1-s^2)^2 := by rw [show c^4 = (c^2)^2 by ring,hc2]
  have ha : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hv := (bernoulli_curve_geometry u).2.2.1
  have hs := Real.hasDerivAt_sin u
  have hc := Real.hasDerivAt_cos u
  have hD := (hasDerivAt_const u (1:ℝ)).add (hs.pow 2)
  have hQ : HasDerivAt bernoulliProfileQ
      ((Real.sqrt 2*‖bernoulliVelocity u‖)*bernoulliProfileP u) u := by
    rw [hv]
    convert! hc.div (hD.sqrt hd0) hr0 using 1
    simp only [bernoulliProfileP,Pi.add_apply,Pi.pow_apply]
    change (Real.sqrt 2*(1/r))*(-Real.sqrt 2*s/d) =
      ((-s)*r-c*((0+2*s^(2-1)*c)/(2*r)))/r^2
    field_simp [hr0,hd0]
    ring_nf
    simp only [ha,hr2,hc2]
    dsimp only [d]
    ring
  have hP : HasDerivAt bernoulliProfileP
      (-(Real.sqrt 2*‖bernoulliVelocity u‖)*(bernoulliProfileQ u)^3) u := by
    rw [hv]
    convert! (hs.const_mul (-Real.sqrt 2)).div hD hd0 using 1
    simp only [bernoulliProfileQ,Pi.add_apply,Pi.pow_apply]
    change -(Real.sqrt 2*(1/r))*(c/r)^3 =
      ((-Real.sqrt 2*c)*d-(-Real.sqrt 2*s)*(0+2*s^(2-1)*c))/d^2
    field_simp [hr0,hd0]
    ring_nf
    simp only [hr4,hc3]
    dsimp only [d]
    ring
  refine ⟨hQ,hP,?_⟩
  change 2*(-Real.sqrt 2*s/d)^2+(c/r)^4 = 1
  field_simp [hr0,hd0]
  ring_nf
  simp only [ha,hr4,hc4]
  dsimp only [d]
  ring

private theorem expander_equation (u : ℝ) :
    arclengthDerivative bernoulliCurve
        (arclengthDerivative bernoulliCurve (planarSignedCurvature bernoulliCurve)) u +
      (1/2:ℝ)*(planarSignedCurvature bernoulliCurve u)^3 +
      (15/2:ℝ)*planarNormalSupport bernoulliCurve u = 0 := by
  have hvel : deriv bernoulliCurve = bernoulliVelocity :=
    funext fun v => (bernoulli_curve_geometry v).1.deriv
  have hacc : deriv bernoulliVelocity = bernoulliAcceleration :=
    funext fun v => (bernoulli_curve_geometry v).2.1.deriv
  have hspeed (v : ℝ) : ‖bernoulliVelocity v‖ ≠ 0 := by
    rw [(bernoulli_curve_geometry v).2.2.1]
    exact div_ne_zero one_ne_zero (ne_of_gt (Real.sqrt_pos.mpr
      (by nlinarith only [sq_nonneg (Real.sin v)])))
  have hk : planarSignedCurvature bernoulliCurve = fun v => 3*bernoulliProfileQ v := by
    funext v
    dsimp only [planarSignedCurvature]
    rw [hvel,hacc,(bernoulli_curve_geometry v).2.2.2.1]
    dsimp only [bernoulliProfileQ]
    ring
  have hh : planarNormalSupport bernoulliCurve u = -(bernoulliProfileQ u)^3 := by
    dsimp only [planarNormalSupport,bernoulliProfileQ]
    rw [hvel]
    exact (bernoulli_curve_geometry u).2.2.2.2.1
  have hk1 : arclengthDerivative bernoulliCurve (planarSignedCurvature bernoulliCurve) =
      fun v => 3*Real.sqrt 2*bernoulliProfileP v := by
    funext v
    dsimp only [arclengthDerivative]
    rw [hk,hvel,((bernoulli_profile_data v).1.const_mul 3).deriv]
    field_simp [hspeed v]
  have hk2 : arclengthDerivative bernoulliCurve
      (arclengthDerivative bernoulliCurve (planarSignedCurvature bernoulliCurve)) u =
        -6*(bernoulliProfileQ u)^3 := by
    dsimp only [arclengthDerivative]
    rw [hk1,hvel,((bernoulli_profile_data u).2.1.const_mul (3*Real.sqrt 2)).deriv]
    field_simp [hspeed u]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    ring
  rw [hk2,hk,hh]
  ring

theorem bernoulli_closed_expander :
    ContDiff ℝ ∞ bernoulliCurve ∧
    Function.Periodic bernoulliCurve (2*Real.pi) ∧
    ∀ u : ℝ, deriv bernoulliCurve u ≠ 0 ∧
      arclengthDerivative bernoulliCurve
          (arclengthDerivative bernoulliCurve (planarSignedCurvature bernoulliCurve)) u +
        (1/2:ℝ)*(planarSignedCurvature bernoulliCurve u)^3 +
        (15/2:ℝ)*planarNormalSupport bernoulliCurve u = 0 := by
  refine ⟨?_,?_,?_⟩
  · have hd : ContDiff ℝ ∞ (fun u : ℝ => 1+(Real.sin u)^2) :=
      contDiff_const.add (Real.contDiff_sin.pow 2)
    have hden (u : ℝ) : 1+(Real.sin u)^2 ≠ 0 := by
      have hp : 0 < 1+(Real.sin u)^2 := by nlinarith only [sq_nonneg (Real.sin u)]
      exact ne_of_gt hp
    have hx := Real.contDiff_cos.div hd hden
    have hy := (Real.contDiff_sin.mul Real.contDiff_cos).div hd hden
    exact (Complex.ofRealCLM.contDiff.comp hx).add
      ((Complex.ofRealCLM.contDiff.comp hy).mul contDiff_const)
  · intro u
    simp only [bernoulliCurve,Real.sin_add_two_pi,Real.cos_add_two_pi]
  · intro u
    refine ⟨?_,expander_equation u⟩
    rw [(bernoulli_curve_geometry u).1.deriv]
    apply norm_pos_iff.mp
    rw [(bernoulli_curve_geometry u).2.2.1]
    exact one_div_pos.mpr (Real.sqrt_pos.mpr
      (by nlinarith only [sq_nonneg (Real.sin u)]))

end Lemniscate
