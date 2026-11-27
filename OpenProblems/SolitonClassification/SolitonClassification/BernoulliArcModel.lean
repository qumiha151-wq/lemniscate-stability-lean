import SolitonClassification.BernoulliArcClock
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.LinearCombination

noncomputable section
open Complex
namespace ClosedSimilarity.BernoulliGeometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

def height (u : ℝ) := Real.sin u / root u
def phase (u : ℝ) : ℂ := (1-I*(Real.cos u:ℂ))/(root u:ℂ)
def beta (u : ℝ) : ℂ := (height u:ℂ)*phase u
def tangent (u : ℝ) : ℂ := I*(phase u)^3
def curvature (u : ℝ) := 3*height u
def slope (u : ℝ) := 6*Real.cos u/(1+Real.cos u^2)

theorem beta_formula (u : ℝ) : beta u=(Real.sin u:ℂ)/(1+I*(Real.cos u:ℂ)) := by
  have r : (root u:ℂ)≠0 := by exact_mod_cast (root_pos u).ne'
  have den : 1+I*(Real.cos u:ℂ)≠0 := by
    intro eq
    have hh := congrArg Complex.re eq
    simp [Complex.mul_re] at hh
  have sq : (root u:ℂ)^2=1+(Real.cos u:ℂ)^2 := by exact_mod_cast root_sq u
  dsimp [beta,height,phase]
  push_cast only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_inv,Complex.ofReal_pow,Complex.ofReal_ofNat]
  field_simp [r,den]
  linear_combination -(Real.sin u:ℂ)*sq-(Real.sin u:ℂ)*(Real.cos u:ℂ)^2*I_sq

theorem droot (u : ℝ) :
    HasDerivAt root (-(Real.cos u*Real.sin u)/root u) u := by
  have d := (((Real.hasDerivAt_cos u).pow 2).const_add 1).sqrt (by change 1+Real.cos u^2≠0; positivity)
  convert! d using 1
  dsimp only [root,Pi.pow_apply]
  ring

theorem dheight (u : ℝ) : HasDerivAt height (2*Real.cos u/root u^3) u := by
  convert! (Real.hasDerivAt_sin u).div (droot u) (root_pos u).ne' using 1
  field_simp [(root_pos u).ne']
  have sc := Real.sin_sq_add_cos_sq u
  linear_combination -(Real.cos u)*((root_sq u)+(sc))

theorem dslope (u : ℝ) : HasDerivAt slope ((-2/9)*curvature u^3/root u) u := by
  have den : 1+Real.cos u^2≠0 := by positivity
  convert! ((Real.hasDerivAt_cos u).const_mul 6).div
    (((Real.hasDerivAt_cos u).pow 2).const_add 1) den using 1
  dsimp only [curvature,height,Pi.pow_apply]
  rw [←root_sq u]
  field_simp [(root_pos u).ne']
  have sc := Real.sin_sq_add_cos_sq u
  linear_combination 54*Real.sin u*((root_sq u)-sc)

theorem dphase (u : ℝ) :
    HasDerivAt phase (I*(Real.sin u:ℂ)/(root u:ℂ)^2*phase u) u := by
  have r : (root u:ℂ)≠0 := by exact_mod_cast (root_pos u).ne'
  have sq : (root u:ℂ)^2=1+(Real.cos u:ℂ)^2 := by exact_mod_cast root_sq u
  convert! ((hasDerivAt_const u (1:ℂ)).sub ((Real.hasDerivAt_cos u).ofReal_comp.const_mul I)).div
    (droot u).ofReal_comp r using 1
  dsimp only [phase,Pi.sub_apply]
  push_cast only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_inv,Complex.ofReal_pow,Complex.ofReal_ofNat]
  field_simp [r]
  linear_combination -I*(Real.sin u:ℂ)*sq-(Real.sin u:ℂ)*(Real.cos u:ℂ)*I_sq

theorem dbeta (u : ℝ) : HasDerivAt beta ((speed u:ℂ)*tangent u) u := by
  convert! (dheight u).ofReal_comp.mul (dphase u) using 1
  dsimp only [speed,tangent,phase,height]
  have r : (root u:ℂ)≠0 := by exact_mod_cast (root_pos u).ne'
  have sc : (Real.sin u:ℂ)^2+(Real.cos u:ℂ)^2=1 := by exact_mod_cast Real.sin_sq_add_cos_sq u
  push_cast only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_inv,Complex.ofReal_pow,Complex.ofReal_ofNat]
  field_simp [r]
  linear_combination -I*(1-I*(Real.cos u:ℂ))*sc+
    (1-I*(Real.cos u:ℂ))*(-2*(Real.cos u:ℂ)+I*(Real.cos u:ℂ)^2)*I_sq

theorem dtangent (u : ℝ) : HasDerivAt tangent
    ((speed u:ℂ)*I*(curvature u:ℂ)*tangent u) u := by
  convert! ((dphase u).pow 3).const_mul I using 1
  dsimp only [speed,curvature,height,tangent]
  push_cast only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_inv,Complex.ofReal_pow,Complex.ofReal_ofNat]
  ring

theorem dcurvature (u : ℝ) : HasDerivAt curvature (slope u*speed u) u := by
  convert! (dheight u).const_mul 3 using 1
  dsimp only [slope,speed]
  rw [←root_sq u]
  ring

theorem tangent_unit (u : ℝ) : ‖tangent u‖=1 := by
  have eq : Complex.normSq (1-I*(Real.cos u:ℂ))=1+Real.cos u^2 := by
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.mul_re,Complex.sub_im,Complex.mul_im,
      Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im]
    ring
  have mag : ‖1-I*(Real.cos u:ℂ)‖=root u := by
    rw [←Complex.sq_norm] at eq
    nlinarith [root_sq u,root_pos u,norm_nonneg (1-I*(Real.cos u:ℂ))]
  simp only [tangent,phase,norm_mul,norm_pow,norm_div,Complex.norm_I,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (root_pos u),mag,div_self (root_pos u).ne',one_pow]

end ClosedSimilarity.BernoulliGeometry
