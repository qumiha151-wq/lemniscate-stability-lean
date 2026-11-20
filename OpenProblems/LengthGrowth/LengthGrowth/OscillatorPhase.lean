import LengthGrowth.OscillatorTurning

noncomputable section
namespace LengthGrowth.OscillatorMean
open Real Set MeasureTheory
set_option maxHeartbeats 600000

theorem primitive_derivative {f : ℝ → ℝ} (h : Continuous f) (t : ℝ) :
    HasDerivAt (fun x => ∫ u in 0..x,f u) (f t) t :=
  intervalIntegral.integral_hasDerivAt_right (h.intervalIntegrable 0 t)
    h.aestronglyMeasurable.stronglyMeasurableAtFilter h.continuousAt

theorem initial_phase {x y : ℝ} (h : x^2+y^2=1) :
    ∃ θ, cos θ=x ∧ sin θ=y := by
  have xcos := cos_arccos (show -1≤x by nlinarith [sq_nonneg y])
    (show x≤1 by nlinarith [sq_nonneg y])
  have xsin : sin (arccos x)=|y| := by
    rw [sin_arccos,show 1-x^2=y^2 by linarith,sqrt_sq_eq_abs]
  by_cases hy : 0≤y
  · exact ⟨arccos x,xcos,xsin.trans (abs_of_nonneg hy)⟩
  · exact ⟨-arccos x,by simpa using xcos,by rw [sin_neg,xsin,abs_of_neg (lt_of_not_ge hy),neg_neg]⟩

/-- A nonsingular lift of a rotating unit vector. The hypotheses are local
derivative equations and one initial unit norm. -/
theorem lift_rotating_pair {X Y w : ℝ → ℝ} (cw : Continuous w)
    (dX : ∀ t,HasDerivAt X (-(w t)*Y t) t)
    (dY : ∀ t,HasDerivAt Y (w t*X t) t) (h0 : (X 0)^2+(Y 0)^2=1) :
    ∃ θ : ℝ → ℝ, (∀ t,HasDerivAt θ (w t) t) ∧ (∀ t,X t=cos (θ t)) ∧
      (∀ t,Y t=sin (θ t)) := by
  obtain ⟨a,ha,hb⟩ := initial_phase h0
  let θ : ℝ → ℝ := fun t => a+∫ u in 0..t,w u
  have dθ (t : ℝ) : HasDerivAt θ (w t) t := (primitive_derivative cw t).const_add a
  let err : ℝ → ℝ := fun t => (X t-cos (θ t))^2+(Y t-sin (θ t))^2
  have derr (t : ℝ) : HasDerivAt err 0 t := by
    have d := (((dX t).sub (dθ t).cos).pow 2).add (((dY t).sub (dθ t).sin).pow 2)
    convert d using 1 <;> first | rfl | simp only [Pi.sub_apply]; ring
  have eqs (t : ℝ) : X t=cos (θ t) ∧ Y t=sin (θ t) := by
    have e := constant_of_zero_velocity derr t
    have e0 : err 0=0 := by simp [err,θ,ha,hb]
    rw [e0] at e
    change (X t-cos (θ t))^2+(Y t-sin (θ t))^2=0 at e
    exact ⟨by nlinarith [sq_nonneg (Y t-sin (θ t))],by nlinarith [sq_nonneg (X t-cos (θ t))]⟩
  exact ⟨θ,dθ,fun t => (eqs t).1,fun t => (eqs t).2⟩

private theorem phase_algebra {x v S c r : ℝ} (hr : 0<r) (hS : 0<S)
    (hsq : S^2=(x+c)^2+orbitOffset c r)
    (hv : 4*v^2=(r^2-(x-c)^2)*((x+c)^2+orbitOffset c r))
    (turn : 2*c*r^2=1+c-2*c^3) :
    ((-2*(-x^3/2+x/4+1/4))*(r*S)-(-2*v)*(r*(2*(x+c)*v/(2*S))))/(r*S)^2 =
      (S/2)*((x-c)/r) := by
  let acc := -x^3/2+x/4+1/4
  have eq1 : -4*acc+(r^2-(x-c)^2)*(x+c) = ((x+c)^2+orbitOffset c r)*(x-c) := by
    dsimp [acc,orbitOffset]
    nlinarith only [turn]
  have eq2 : -4*acc*S^2+(4*v^2)*(x+c)=S^4*(x-c) := by
    rw [show S^4=(S^2)^2 by ring,hsq,hv]
    linear_combination ((x+c)^2+orbitOffset c r)*eq1
  calc
    _ = (-4*acc*S^2+(4*v^2)*(x+c))/(2*r*S^3) := by
      dsimp [acc]
      field_simp [hr.ne',hS.ne']
      ring
    _ = _ := by rw [eq2]; field_simp [hr.ne',hS.ne']

namespace QuarticOrbit
variable (o : QuarticOrbit)

theorem actual_phase {c r : ℝ} (hr : 0<r) (hp : quarticPotential (c+r)=o.energy 0)
    (hm : quarticPotential (c-r)=o.energy 0) :
    ∃ θ : ℝ → ℝ, (∀ t,HasDerivAt θ (√((o.z t+c)^2+orbitOffset c r)/2) t) ∧
      (∀ t,o.z t=c+r*cos (θ t)) := by
  obtain ⟨_,_,turn,hd⟩ := turning_parameters hr (hp.trans hm.symm)
  let S : ℝ → ℝ := fun t => √((o.z t+c)^2+orbitOffset c r)
  let X : ℝ → ℝ := fun t => (o.z t-c)/r
  let Y : ℝ → ℝ := fun t => (-2*o.v t)/(r*S t)
  let w : ℝ → ℝ := fun t => S t/2
  have pos (t : ℝ) : 0<(o.z t+c)^2+orbitOffset c r := by nlinarith only [hd,sq_nonneg (o.z t+c)]
  have ps (t : ℝ) : 0<S t := sqrt_pos.mpr (pos t)
  have ss (t : ℝ) : (S t)^2=(o.z t+c)^2+orbitOffset c r := sq_sqrt (pos t).le
  have dS (t : ℝ) : HasDerivAt S (2*(o.z t+c)*o.v t/(2*S t)) t := by
    convert (((((o.dz t).add_const c).pow 2).add_const (orbitOffset c r)).sqrt (pos t).ne') using 1 <;>
      first | rfl | dsimp only [Pi.pow_apply,S]; ring
  have cS : Continuous S := continuous_iff_continuousAt.mpr (fun t => (dS t).continuousAt)
  have dX (t : ℝ) : HasDerivAt X (-(w t)*Y t) t := by
    have e : -(w t)*Y t=o.v t/r := by dsimp only [w,Y]; field_simp [hr.ne',(ps t).ne']
    rw [e]
    exact ((o.dz t).sub_const c).div_const r
  have dY (t : ℝ) : HasDerivAt Y (w t*X t) t := by
    have d := ((o.dv t).const_mul (-2)).div ((dS t).const_mul r) (mul_ne_zero hr.ne' (ps t).ne')
    exact (phase_algebra hr (ps t) (ss t) (o.velocity_squared hr hp hm t) turn) ▸ d
  have unit : (X 0)^2+(Y 0)^2=1 := by
    have v := o.velocity_squared hr hp hm 0
    rw [← ss 0] at v
    dsimp only [X,Y]
    field_simp [hr.ne',(ps 0).ne']
    nlinarith only [v]
  obtain ⟨θ,hθ,hx,_⟩ := lift_rotating_pair (cS.div_const 2) dX dY unit
  refine ⟨θ,hθ,fun t => ?_⟩
  have eq := (div_eq_iff hr.ne').mp (hx t)
  linarith only [eq]

end QuarticOrbit
end LengthGrowth.OscillatorMean
