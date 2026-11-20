import LengthGrowth.ActualFlow.ForcePersistence

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow

private theorem derivative_eighth {P : ℝ} (hP : 0<P) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f P) {s : ℝ} (hs : s∈Icc 0 P) :
    deriv f s ^ 8 ≤ 16*(∫ x in 0..P,f x^2)*(∫ x in 0..P,deriv (deriv f) x^2)^3 := by
  let g := deriv f
  let h := deriv g
  have cg : ContDiff ℝ ∞ g := (contDiff_infty_iff_deriv.mp hf).2
  have ch : ContDiff ℝ ∞ h := (contDiff_infty_iff_deriv.mp cg).2
  have pg := actual_deriv_periodic hp (hf.differentiable (by simp))
  have ib := periodic_mul_integration_by_parts hf cg hp pg
  have forceCS := interval_integral_mul_sq_le hf.continuous ch.continuous hP.le
  let J := ∫ x in 0..P,g x^2
  let D := ∫ x in 0..P,f x^2
  let Y := ∫ x in 0..P,h x^2
  have ib' : (∫ x in 0..P, f x * h x) = -J := by simpa [h,J,g,pow_two] using ib
  have jcs : J^2 ≤ D*Y := by simpa only [ib',neg_sq] using forceCS
  obtain ⟨z,hz,hzero⟩ := exists_deriv_eq_zero hP hf.continuous.continuousOn
    (show f 0=f P by simpa using (hp 0).symm)
  have hd (x : ℝ) : HasDerivAt (fun u => g u ^ 2) (2*(g x*h x)) x := by
    convert! ((cg.differentiable (by simp) x).hasDerivAt.pow 2) using 1
    dsimp [h]
    ring
  have osc' := interval_oscillation_le hd
    ((cg.continuous.mul ch.continuous).const_mul 2) hs (show z∈Icc 0 P from ⟨hz.1.le,hz.2.le⟩)
  have eqn (x : ℝ) : ‖2*(g x*h x)‖=2*|g x*h x| := by
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  let B := ∫ x in 0..P, |g x*h x|
  have osc : g s^2 ≤ 2*B := calc
    _ = ‖g s^2-g z^2‖ := by
      rw [show g z=0 from hzero]
      simp [Real.norm_eq_abs]
    _ ≤ ∫ x in 0..P, ‖2*(g x*h x)‖ := osc'
    _ = _ := by simp_rw [eqn,intervalIntegral.integral_const_mul]; rfl
  have cs := interval_integral_mul_sq_le cg.continuous.abs ch.continuous.abs hP.le
  simp_rw [← abs_mul,sq_abs] at cs
  have bcs : B^2≤J*Y := cs
  have h4 : g s^4 ≤ 4*J*Y := by
    have q := mul_self_le_mul_self (sq_nonneg (g s)) osc
    change g s^2*(g s^2) ≤ 2*B*(2*B) at q
    nlinarith only [q,bcs]
  have q := mul_self_le_mul_self (by positivity : 0≤g s^4) h4
  have hprod := mul_le_mul_of_nonneg_right jcs (sq_nonneg Y)
  change g s^8 ≤ 16*D*Y^3
  nlinarith only [q,hprod]

/-- A period-independent estimate for the angular speed of the real normal
material flow, evaluated from position on an arbitrary-speed slice. -/
theorem ForwardImmersion.material_force_angular_speed (c : ForwardImmersion) {t u : ℝ}
    (ht : 0≤t) (hu : u∈Icc 0 c.period) :
    arcDerivative (c.position t) (force (c.position t)) u ^ 8 ≤
      16*c.dissipation t*(c.forceSecondMass t)^3 := by
  let p := c.regularPositionAt ht
  let F := force p.position
  let G := arcDerivative p.position F
  let H := arcDerivative p.position G
  let f := fun x => F (p.arclengthInverse x)
  have cF : ContDiff ℝ ∞ F := force_smooth p.smooth p.regular
  have cG : ContDiff ℝ ∞ G := arcDerivative_smooth p.smooth p.regular cF
  have cH : ContDiff ℝ ∞ H := arcDerivative_smooth p.smooth p.regular cG
  have cf : ContDiff ℝ ∞ f := cF.comp p.inverse_smooth
  have fp : Function.Periodic f p.length := by
    intro x
    dsimp only [f,F]
    rw [p.inverse_add_length,force_periodic p.smooth p.regular p.periodic]
  have eqg : deriv f = fun x => G (p.arclengthInverse x) :=
    funext (deriv_comp_arclength_inverse p.inverse_hasDerivAt (cF.differentiable (by simp)))
  have eqh : deriv (deriv f) = fun x => H (p.arclengthInverse x) := by
    rw [eqg]
    exact funext (deriv_comp_arclength_inverse p.inverse_hasDerivAt (cG.differentiable (by simp)))
  have slab : p.arclength u∈Icc 0 p.length := by
    constructor
    · simpa only [p.arclength_zero] using p.arclength_strictMono.monotone hu.1
    · rw [← p.arclength_length]
      exact p.arclength_strictMono.monotone hu.2
  have est := derivative_eighth p.length_pos cf fp slab
  simp_rw [eqh,eqg,p.arclength_inverse_right] at est
  have eD := p.integral_comp_inverse (f:=fun z => F z^2) (cF.continuous.pow 2)
  have eY := p.integral_comp_inverse (f:=fun z => H z^2) (cH.continuous.pow 2)
  change G u^8 ≤ 16*(∫ x in 0..p.length,F (p.arclengthInverse x)^2)*
    (∫ x in 0..p.length,H (p.arclengthInverse x)^2)^3 at est
  rw [eD,eY] at est
  exact est

#print axioms ForwardImmersion.material_force_angular_speed
end LengthGrowth.ActualFlow
