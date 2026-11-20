import LengthGrowth.OscillatorTime
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Global existence with prescribed position and velocity, by the inverse
of the positive angular time primitive. -/
noncomputable section
namespace LengthGrowth.OscillatorMean
open Real Set MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 700000

private theorem inverse_clock {g : ℝ → ℝ} {p : ℝ} (hp : 0<p) (cg : Continuous g)
    (pg : Function.Periodic g p) (pos : ∀ t,0<g t) (a : ℝ) :
    ∃ θ : ℝ → ℝ, θ 0=a ∧ ∀ t,HasDerivAt θ (g (θ t))⁻¹ t := by
  let F : ℝ → ℝ := fun x => ∫ u in 0..x,g u
  have dF (x : ℝ) : HasDerivAt F (g x) x := primitive_derivative cg x
  have cF : Continuous F := continuous_iff_continuousAt.mpr (fun x => (dF x).continuousAt)
  have top : Tendsto F atTop atTop := pg.tendsto_atTop_intervalIntegral_of_pos'
    (cg.intervalIntegrable 0 p) pos hp
  have bot : Tendsto F atBot atBot := pg.tendsto_atBot_intervalIntegral_of_pos'
    (cg.intervalIntegrable 0 p) pos hp
  let e : ℝ ≃o ℝ := (strictMono_of_hasDerivAt_pos dF pos).orderIsoOfSurjective F (cF.surjective top bot)
  have self (x : ℝ) : F (e.symm x)=x := e.apply_symm_apply x
  have ds (x : ℝ) : HasDerivAt (fun u => e.symm u) (g (e.symm x))⁻¹ x :=
    HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt (dF (e.symm x))
      (pos _).ne' (Eventually.of_forall self)
  refine ⟨fun t => e.symm (t+F a),?_,fun t => ?_⟩
  · simp only [zero_add]
    exact e.symm_apply_apply a
  · exact (ds (t+F a)).comp_add_const t (F a)

private theorem parameterized_orbit {c r : ℝ} (hd : 0<orbitOffset c r)
    (turn : 2*c*r^2=1+c-2*c^3) (θ : ℝ → ℝ)
    (hθ : ∀ t,HasDerivAt θ (√((anglePosition c r (θ t)+c)^2+orbitOffset c r)/2) t) :
    ∃ o : QuarticOrbit, (∀ t,o.z t=anglePosition c r (θ t)) ∧
      (∀ t,o.v t=(-r*sin (θ t))*(√((anglePosition c r (θ t)+c)^2+orbitOffset c r)/2)) := by
  let z : ℝ → ℝ := fun t => anglePosition c r (θ t)
  let S : ℝ → ℝ := fun t => √((z t+c)^2+orbitOffset c r)
  let v : ℝ → ℝ := fun t => (-r*sin (θ t))*(S t/2)
  have dZ (t : ℝ) : HasDerivAt z (v t) t := by
    have h := (((hθ t).cos.const_mul r).const_add c)
    convert h using 1 <;> first | rfl | dsimp [v,S,z,anglePosition]; ring
  have rad (t : ℝ) : 0<(z t+c)^2+orbitOffset c r := by positivity
  have ps (t : ℝ) : 0<S t := sqrt_pos.mpr (rad t)
  have ss (t : ℝ) : (S t)^2=(z t+c)^2+orbitOffset c r := sq_sqrt (rad t).le
  have dS (t : ℝ) : HasDerivAt S ((z t+c)*v t/S t) t := by
    have h := ((((dZ t).add_const c).pow 2).add_const (orbitOffset c r)).sqrt (rad t).ne'
    convert h using 1 <;> first | rfl | dsimp only [Pi.pow_apply,S];ring
  have dV (t : ℝ) : HasDerivAt v (-(z t)^3/2+z t/4+1/4) t := by
    let a := θ t
    have ht : HasDerivAt θ (S t/2) t := hθ t
    have h := ((ht.sin.const_mul (-r)).mul ((dS t).div_const 2))
    have alg : (-r*(cos a*(S t/2)))*(S t/2)+(-r*sin a)*(((z t+c)*v t/S t)/2) =
        -(z t)^3/2+z t/4+1/4 := by
      have tr := sin_sq_add_cos_sq a
      have pos := ps t
      have zz : z t=c+r*cos a := rfl
      have key : (r^2-(z t-c)^2)*(z t+c)-(z t-c)*(S t)^2 =
          4*(-(z t)^3/2+z t/4+1/4) := by
        rw [ss]
        dsimp [orbitOffset]
        nlinarith only [turn]
      calc
        _ = ((r*sin a)^2*(z t+c)-r*cos a*(S t)^2)/4 := by
          change (-r*(cos a*(S t/2)))*(S t/2)+
              (-r*sin a)*(((z t+c)*((-r*sin a)*(S t/2))/S t)/2)=_
          field_simp [pos.ne']
          ring
        _ = _ := by
          rw [show (r*sin a)^2=r^2-(z t-c)^2 by rw [zz]; linear_combination r^2*tr,
            show r*cos a=z t-c by rw [zz];ring]
          linarith only [key]
    exact alg ▸ h
  exact ⟨⟨z,v,dZ,dV⟩,fun _ => rfl,fun _ => rfl⟩

theorem exists_orbit_with_data (x v₀ : ℝ) :
    ∃ o : QuarticOrbit,o.z 0=x ∧ o.v 0=v₀ := by
  let H := v₀^2/2+quarticPotential x
  by_cases high : quarticPotential 1<H
  · obtain ⟨c,r,hr,hp,hm⟩ := turning_values high
    obtain ⟨_,_,turn,hd⟩ := turning_parameters hr (hp.trans hm.symm)
    have pos : 0<orbitOffset c r := by linarith
    let S := √((x+c)^2+orbitOffset c r)
    have rad : 0<(x+c)^2+orbitOffset c r := by positivity
    have ps : 0<S := sqrt_pos.mpr rad
    have ss : S^2=(x+c)^2+orbitOffset c r := sq_sqrt rad.le
    have vh : 4*v₀^2=(r^2-(x-c)^2)*S^2 := by
      rw [ss]
      dsimp [H,quarticPotential] at hp
      dsimp [orbitOffset]
      linear_combination -8*hp+(2*c+2*r-2*x)*turn
    have unit : ((x-c)/r)^2+((-2*v₀)/(r*S))^2=1 := by
      field_simp [hr.ne',ps.ne']
      nlinarith only [vh]
    obtain ⟨a,ca,sa⟩ := initial_phase unit
    let g : ℝ → ℝ := fun t => 2*inverseRadical c r t
    have cg : Continuous g := (inv_radical_cont pos).const_mul 2
    have pg : Function.Periodic g (2*π) := by
      intro y
      simp only [g,inverseRadical,anglePosition,cos_add_two_pi]
    have gp (t : ℝ) : 0<g t := by dsimp [g,inverseRadical]; positivity
    obtain ⟨θ,θ0,dθ⟩ := inverse_clock (by positivity) cg pg gp a
    have d (t : ℝ) : HasDerivAt θ (√((anglePosition c r (θ t)+c)^2+orbitOffset c r)/2) t := by
      have eq : (g (θ t))⁻¹=√((anglePosition c r (θ t)+c)^2+orbitOffset c r)/2 := by
        dsimp [g,inverseRadical]
        rw [mul_inv_rev,one_div,inv_inv,div_eq_mul_inv]
      exact eq ▸ dθ t
    obtain ⟨o,oz,ov⟩ := parameterized_orbit pos turn θ d
    have x0 : anglePosition c r (θ 0)=x := by
      dsimp [anglePosition]
      rw [θ0,ca]
      field_simp [hr.ne']
      ring
    refine ⟨o,(oz 0).trans x0,?_⟩
    rw [ov,x0,θ0,sa]
    change (-r*((-2*v₀)/(r*S)))*(S/2)=v₀
    field_simp [hr.ne',ps.ne']
  · have hx : x=1 := by
      dsimp [H] at high
      nlinarith only [le_of_not_gt high,potential_distance x,sq_nonneg v₀,sq_nonneg (x-1)]
    have hv : v₀=0 := by
      dsimp [H] at high
      rw [hx] at high
      nlinarith only [le_of_not_gt high]
    let o : QuarticOrbit := ⟨fun _ => 1,fun _ => 0,fun t => hasDerivAt_const t 1,
      fun t => by norm_num; exact hasDerivAt_const t 0⟩
    exact ⟨o,hx.symm,hv.symm⟩

theorem QuarticOrbit.position_C2 (o : QuarticOrbit) : ContDiff ℝ 2 o.z := by
  have cz : Continuous o.z := continuous_iff_continuousAt.mpr (fun t => (o.dz t).continuousAt)
  have ca : Continuous (fun t => -(o.z t)^3/2+o.z t/4+1/4) :=
    ((((cz.pow 3).neg.div_const 2).add (cz.div_const 4)).add continuous_const)
  have cv : ContDiff ℝ 1 o.v := contDiff_one_iff_deriv.mpr
    ⟨fun t => (o.dv t).differentiableAt,by rw [show deriv o.v=_ from funext (fun t => (o.dv t).deriv)]; exact ca⟩
  apply (contDiff_succ_iff_deriv (n:=1)).mpr
  refine ⟨fun t => (o.dz t).differentiableAt,by simp,?_⟩
  rwa [show deriv o.z=o.v from funext (fun t => (o.dz t).deriv)]

theorem exists_global_c2_from_data (x v : ℝ) :
    ∃ z : ℝ → ℝ, ContDiff ℝ 2 z ∧ z 0=x ∧ deriv z 0=v ∧
      ∀ t,deriv (deriv z) t=-(z t)^3/2+z t/4+1/4 := by
  obtain ⟨o,hx,hv⟩ := exists_orbit_with_data x v
  refine ⟨o.z,o.position_C2,hx,(o.dz 0).deriv.trans hv,fun t => ?_⟩
  rw [show deriv o.z=o.v from funext (fun t => (o.dz t).deriv)]
  exact (o.dv t).deriv

end LengthGrowth.OscillatorMean

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms `LengthGrowth.OscillatorMean.exists_global_c2_from_data) do
    unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains ax do
      throwError "Unexpected axiom {ax}"
  logInfo "OSCILLATOR_EXISTENCE_AUDIT: global actual C2 solution for arbitrary prescribed position and velocity."
