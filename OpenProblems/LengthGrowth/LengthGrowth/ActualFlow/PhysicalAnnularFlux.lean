import LengthGrowth.ActualFlow.StressAnnularTransfer

noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace LengthGrowth.ActualFlow

/-- Regularized norm of the elastic stress in the original curve parameter. -/
def fluxRadius (a k p : ℝ) := Real.sqrt (a^4+p^2+k^4/4)

private theorem flux_radius_pos {a : ℝ} (ha : 0<a) (k p : ℝ) : 0<fluxRadius a k p := by
  unfold fluxRadius
  positivity

private theorem radius_slope {a : ℝ} (ha : 0<a) {k p : ℝ → ℝ} {x v l : ℝ}
    (dk : HasDerivAt k (v*p x) x) (dp : HasDerivAt p (v*l) x) :
    HasDerivAt (fun y => fluxRadius a (k y) (p y))
      (v*p x*(l+k x^3/2)/fluxRadius a (k x) (p x)) x := by
  have d := (((dp.pow 2).const_add (a^4)).add ((dk.pow 4).div_const 4)).sqrt
    (show a^4+p x^2+k x^4/4≠0 by positivity)
  apply d.congr_deriv
  simp only [Nat.cast_ofNat, Nat.reduceSub, fluxRadius,Pi.add_apply,Pi.pow_apply]
  ring

private def current (a k p f g q R : ℝ) :=
  a^2*((k^4/4-a^4)*f^2/R^3+f*(k^2*q-2*k*p*g)/(2*R^3))
private def divergence (a k p f g q R : ℝ) :=
  a^2*((2*k*p*f*g+k^2*g^2+k^2*f*q)/(2*R^3)-
    3*k^2*p*f^2*g/(2*R^5))

/-- The spatial part of the scale-current identity on an arbitrary genuine
regular closed plane immersion, including degenerate zero-stress points. -/
theorem physical_scale_flux_by_parts {γ : ℝ → ℂ} {P a : ℝ} (ha : 0<a)
    (smooth : ContDiff ℝ ∞ γ) (reg : ∀u, deriv γ u≠0) (per : Function.Periodic γ P) :
    let k := curvature γ
    let p := curvatureGradient γ
    let f := force γ
    let g := arcDerivative γ f
    let q := arcDerivative γ g
    let R := fun u => fluxRadius a (k u) (p u)
    (∫u in 0..P, a^2*((k u^4/4-a^4)*f u^2/R u^3+
        f u*(k u^2*q u-2*k u*p u*g u)/(2*R u^3))*speed γ u) =
    ∫u in 0..P, a^2*((k u^4/4-a^4)*f u^2/R u^3-k u^2*g u^2/(2*R u^3)-
        2*k u*p u*f u*g u/R u^3+3*k u^2*p u*f u^2*g u/(2*R u^5))*speed γ u := by
  let k := curvature γ
  let p := curvatureGradient γ
  let f := force γ
  let g := arcDerivative γ f
  let q := arcDerivative γ g
  let v := speed γ
  let R := fun u => fluxRadius a (k u) (p u)
  let B := fun u => (a^2*k u^2*f u*g u)/(2*R u^3)
  let b := fun u => divergence a (k u) (p u) (f u) (g u) (q u) (R u)*v u
  let A := fun u => current a (k u) (p u) (f u) (g u) (q u) (R u)*v u
  have sk := curvature_smooth smooth reg
  have sp := curvatureGradient_smooth smooth reg
  have sf := force_smooth smooth reg
  have sg := arcDerivative_smooth smooth reg sf
  have sq := arcDerivative_smooth smooth reg sg
  have ck : Continuous k := sk.continuous
  have cp : Continuous p := sp.continuous
  have cf : Continuous f := sf.continuous
  have cg : Continuous g := sg.continuous
  have cq : Continuous q := sq.continuous
  have cv : Continuous v := (speed_smooth smooth reg).continuous
  have cr : Continuous R := by dsimp only [R,fluxRadius]; fun_prop
  have pos (u : ℝ) : 0<R u := flux_radius_pos ha _ _
  have nr (u : ℝ) : R u≠0 := (pos u).ne'
  have cb : Continuous b := by
    dsimp only [b,divergence]
    fun_prop (disch := intro x; exact mul_ne_zero (by norm_num) (pow_ne_zero _ (nr x)))
  have ca : Continuous A := by
    dsimp only [A,current]
    fun_prop (disch := intro x; first | exact pow_ne_zero _ (nr x) |
      exact mul_ne_zero (by norm_num) (pow_ne_zero _ (nr x)))
  have hb (u : ℝ) : HasDerivAt B (b u) u := by
    have dk : HasDerivAt k (v u*p u) u := curvature_hasDerivAt smooth reg u
    have dp : HasDerivAt p (v u*curvatureSecond γ u) u := curvatureGradient_hasDerivAt smooth reg u
    have df : HasDerivAt f (v u*g u) u :=
      hasDerivAt_speed_smul_arcDerivative reg (sf.differentiable (by simp)) u
    have dg : HasDerivAt g (v u*q u) u :=
      hasDerivAt_speed_smul_arcDerivative reg (sg.differentiable (by simp)) u
    have dr : HasDerivAt R (v u*p u*f u/R u) u := radius_slope ha dk dp
    apply (((((dk.pow 2).const_mul (a^2)).mul df).mul dg).div
      ((dr.pow 3).const_mul 2) (mul_ne_zero (by norm_num) (pow_ne_zero _ (nr u)))).congr_deriv
    simp only [b,divergence,Pi.pow_apply,Pi.mul_apply, Nat.cast_ofNat, Nat.reduceSub]
    field_simp [nr u]
  have pk := curvature_periodic smooth reg per
  have pp := curvatureGradient_periodic smooth reg per
  have pf := force_periodic smooth reg per
  have pg := arcDerivative_periodic smooth per (sf.differentiable (by simp)) pf
  have periodic : Function.Periodic B P := by
    intro u
    simp only [B,R,k,p,f,g,pk u,pp u,pf u,pg u]
  have zero := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=P)
    (fun u _ => hb u) (cb.intervalIntegrable _ _)
  rw [show B P=B 0 by simpa only [zero_add] using periodic 0,sub_self] at zero
  calc
    _ = ∫u in 0..P, A u-b u := by
      rw [intervalIntegral.integral_sub (ca.intervalIntegrable _ _) (cb.intervalIntegrable _ _),
        zero,sub_zero]
      rfl
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only [A,b,current,divergence]
      change _ = a^2*((k u^4/4-a^4)*f u^2/R u^3-k u^2*g u^2/(2*R u^3)-
        2*k u*p u*f u*g u/R u^3+3*k u^2*p u*f u^2*g u/(2*R u^5))*v u
      field_simp [nr u]
      ring

end LengthGrowth.ActualFlow
#print axioms LengthGrowth.ActualFlow.physical_scale_flux_by_parts
