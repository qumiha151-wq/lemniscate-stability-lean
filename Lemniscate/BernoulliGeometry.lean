import Lemniscate.Algebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Norm

/-! Differential geometry of the explicit Bernoulli lemniscate, with the
oriented plane identified with the complex numbers. The normal is i times
the unit tangent, so signed curvature is Im(conj(velocity)*acceleration)
divided by speed cubed. -/
namespace Lemniscate
open Complex
open scoped ComplexConjugate

noncomputable def bernoulliCurve (u : ℝ) : ℂ :=
  ((Real.cos u/(1+(Real.sin u)^2):ℝ):ℂ) +
    ((Real.sin u*Real.cos u/(1+(Real.sin u)^2):ℝ):ℂ)*I

noncomputable def bernoulliVelocity (u : ℝ) : ℂ :=
  ((-Real.sin u*(3-(Real.sin u)^2)/(1+(Real.sin u)^2)^2:ℝ):ℂ) +
    (((1-3*(Real.sin u)^2)/(1+(Real.sin u)^2)^2:ℝ):ℂ)*I

noncomputable def bernoulliAcceleration (u : ℝ) : ℂ :=
  ((Real.cos u*(-3+12*(Real.sin u)^2-(Real.sin u)^4)/(1+(Real.sin u)^2)^3:ℝ):ℂ) +
    ((Real.sin u*Real.cos u*(-10+6*(Real.sin u)^2)/(1+(Real.sin u)^2)^3:ℝ):ℂ)*I

private theorem denominator_pos (u : ℝ) : 0 < 1+(Real.sin u)^2 := by
  nlinarith only [sq_nonneg (Real.sin u)]

private theorem curve_deriv (u : ℝ) : HasDerivAt bernoulliCurve (bernoulliVelocity u) u := by
  have hs := Real.hasDerivAt_sin u
  have hc := Real.hasDerivAt_cos u
  have hd := (hasDerivAt_const u (1:ℝ)).add (hs.pow 2)
  have hd0 := ne_of_gt (denominator_pos u)
  have hcs : (Real.cos u)^2 = 1-(Real.sin u)^2 := by
    nlinarith only [Real.sin_sq_add_cos_sq u]
  have hx : HasDerivAt (fun v : ℝ => Real.cos v/(1+(Real.sin v)^2))
      (-Real.sin u*(3-(Real.sin u)^2)/(1+(Real.sin u)^2)^2) u := by
    convert! hc.div hd hd0 using 1
    simp only [Pi.add_apply,Pi.pow_apply]
    field_simp [hd0]
    ring_nf
    rw [hcs]
    ring
  have hy : HasDerivAt (fun v : ℝ => Real.sin v*Real.cos v/(1+(Real.sin v)^2))
      ((1-3*(Real.sin u)^2)/(1+(Real.sin u)^2)^2) u := by
    convert! (hs.mul hc).div hd hd0 using 1
    simp only [Pi.add_apply,Pi.mul_apply,Pi.pow_apply]
    field_simp [hd0]
    ring_nf
    rw [hcs]
    ring
  exact hx.ofReal_comp.add (hy.ofReal_comp.mul_const I)

private theorem velocity_deriv (u : ℝ) :
    HasDerivAt bernoulliVelocity (bernoulliAcceleration u) u := by
  have hs := Real.hasDerivAt_sin u
  have hd := (hasDerivAt_const u (1:ℝ)).add (hs.pow 2)
  have hd0 := ne_of_gt (denominator_pos u)
  have hx : HasDerivAt
      (fun v : ℝ => -Real.sin v*(3-(Real.sin v)^2)/(1+(Real.sin v)^2)^2)
      (Real.cos u*(-3+12*(Real.sin u)^2-(Real.sin u)^4)/(1+(Real.sin u)^2)^3) u := by
    convert! (hs.neg.mul ((hasDerivAt_const u (3:ℝ)).sub (hs.pow 2))).div
      (hd.pow 2) (pow_ne_zero 2 hd0) using 1
    simp only [Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.neg_apply,Pi.pow_apply]
    field_simp [hd0]
    ring
  have hy : HasDerivAt
      (fun v : ℝ => (1-3*(Real.sin v)^2)/(1+(Real.sin v)^2)^2)
      (Real.sin u*Real.cos u*(-10+6*(Real.sin u)^2)/(1+(Real.sin u)^2)^3) u := by
    convert! ((hasDerivAt_const u (1:ℝ)).sub ((hs.pow 2).const_mul 3)).div
      (hd.pow 2) (pow_ne_zero 2 hd0) using 1
    simp only [Pi.add_apply,Pi.sub_apply,Pi.pow_apply]
    field_simp [hd0]
    ring
  exact hx.ofReal_comp.add (hy.ofReal_comp.mul_const I)

theorem bernoulli_curve_geometry (u : ℝ) :
    HasDerivAt bernoulliCurve (bernoulliVelocity u) u ∧
    HasDerivAt bernoulliVelocity (bernoulliAcceleration u) u ∧
    ‖bernoulliVelocity u‖ = 1/Real.sqrt (1+(Real.sin u)^2) ∧
    (conj (bernoulliVelocity u)*bernoulliAcceleration u).im / ‖bernoulliVelocity u‖^3 =
      3*Real.cos u/Real.sqrt (1+(Real.sin u)^2) ∧
    -(conj (bernoulliCurve u)*bernoulliVelocity u).im / ‖bernoulliVelocity u‖ =
      -(Real.cos u/Real.sqrt (1+(Real.sin u)^2))^3 ∧
    (conj (bernoulliCurve u)*bernoulliVelocity u).re / ‖bernoulliVelocity u‖ =
      -2*Real.sin u*Real.cos u/(Real.sqrt (1+(Real.sin u)^2))^3 := by
  let d := 1+(Real.sin u)^2
  let r := Real.sqrt d
  have hd : 0 < d := denominator_pos u
  have hd0 := ne_of_gt hd
  have hr0 : r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd)
  have hr2 : r^2 = d := Real.sq_sqrt hd.le
  have hn : normSq (bernoulliVelocity u) = 1/d := by
    simp only [bernoulliVelocity,Complex.normSq_apply,Complex.add_re,Complex.add_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,mul_one,add_zero,zero_add]
    dsimp only [d]
    field_simp [hd0]
    ring
  have hv : ‖bernoulliVelocity u‖ = 1/r := by
    rw [Complex.norm_def,hn,Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1),Real.sqrt_one]
  have hcross : (conj (bernoulliVelocity u)*bernoulliAcceleration u).im =
      3*Real.cos u/d^2 := by
    simp only [bernoulliVelocity,bernoulliAcceleration,Complex.mul_re,Complex.mul_im,
      Complex.add_re,Complex.add_im,Complex.conj_re,Complex.conj_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      mul_zero,mul_one,add_zero,zero_add]
    dsimp only [d]
    field_simp [hd0]
    ring
  have htan : (conj (bernoulliCurve u)*bernoulliVelocity u).re =
      -2*Real.sin u*Real.cos u/d^2 := by
    simp only [bernoulliCurve,bernoulliVelocity,Complex.mul_re,Complex.mul_im,
      Complex.add_re,Complex.add_im,Complex.conj_re,Complex.conj_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      mul_zero,mul_one,add_zero,zero_add]
    dsimp only [d]
    field_simp [hd0]
    ring
  have hnormal : (conj (bernoulliCurve u)*bernoulliVelocity u).im =
      (Real.cos u)^3/d^2 := by
    have hcs : (Real.cos u)^2 = 1-(Real.sin u)^2 := by
      nlinarith only [Real.sin_sq_add_cos_sq u]
    simp only [bernoulliCurve,bernoulliVelocity,Complex.mul_re,Complex.mul_im,
      Complex.add_re,Complex.add_im,Complex.conj_re,Complex.conj_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      mul_zero,mul_one,add_zero,zero_add]
    dsimp only [d]
    field_simp [hd0]
    ring_nf
    simp only [show (Real.cos u)^3 = Real.cos u*(Real.cos u)^2 by ring,hcs]
    ring
  refine ⟨curve_deriv u,velocity_deriv u,hv,?_,?_,?_⟩
  · rw [hcross,hv]
    change (3*Real.cos u/d^2)/(1/r)^3 = 3*Real.cos u/r
    rw [← hr2]
    field_simp [hr0]
  · rw [hnormal,hv]
    change -((Real.cos u)^3/d^2)/(1/r) = -(Real.cos u/r)^3
    rw [← hr2]
    field_simp [hr0]
  · rw [htan,hv]
    change (-2*Real.sin u*Real.cos u/d^2)/(1/r) = -2*Real.sin u*Real.cos u/r^3
    rw [← hr2]
    field_simp [hr0]

end Lemniscate
