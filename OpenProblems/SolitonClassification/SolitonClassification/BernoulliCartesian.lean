import SolitonClassification.CubicSupportClassification
import Mathlib.Analysis.Complex.RealDeriv

/-! The actual position of the cubic-force profile satisfies the Cartesian
Bernoulli quartic in the tangent frame at its positive centre crossing. -/
noncomputable section
namespace ClosedSimilarity.ClosedUnitFrenetCurve
open Complex
open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

private def tang (C : ClosedUnitFrenetCurve) (s : ℝ) : ℂ :=
  (C.tx s:ℂ)+(C.ty s:ℂ)*I
private def pos (C : ClosedUnitFrenetCurve) (s : ℝ) : ℂ :=
  (C.x s:ℂ)+(C.y s:ℂ)*I
private def stress (C : ClosedUnitFrenetCurve) (s : ℝ) : ℂ :=
  (C.v s:ℂ)-I*(C.k s:ℂ)^2/3

private theorem imaginary_quartic (C : ClosedUnitFrenetCurve)
    {s₀ b : ℝ} (hb : 0<b) (hb2 : b^2=6/5)
    (hsx : C.x s₀=0) (hsy : C.y s₀=0) (hsk : C.k s₀=0) (hsv : C.v s₀=b)
    (pv : ∀ t,C.normalSupport t= -5/18*C.k t^3)
    (dv : ∀ t,HasDerivAt C.v (-2/9*C.k t^3) t) :
    ∀ t,b*(C.x t^2+C.y t^2)^2 =
      6*(C.x t*C.tx s₀+C.y t*C.ty s₀)*(C.y t*C.tx s₀-C.x t*C.ty s₀) := by
  have en (t : ℝ) : C.v t^2+C.k t^4/9=b^2 := by
    let E (r : ℝ) := C.v r^2+C.k r^4/9
    have dE (r : ℝ) : HasDerivAt E 0 r := by
      convert! ((dv r).pow 2).add (((C.dk r).pow 4).div_const 9) using 1
      ring
    have e := is_const_of_deriv_eq_zero (fun r => (dE r).differentiableAt)
      (fun r => (dE r).deriv) t s₀
    simpa [E,hsk,hsv] using e
  have qv (t : ℝ) : C.tangentSupport t=5/6*C.k t*C.v t := by
    let Q (r : ℝ) := C.tangentSupport r-5/6*C.k r*C.v r
    have dQ (r : ℝ) : HasDerivAt Q 0 r := by
      convert! (C.tangentSupport_hasDerivAt r).sub
        ((((C.dk r).const_mul (5/6)).mul (dv r))) using 1
      rw [pv r]
      linear_combination (5/6)*(en r)+(5/6)*hb2
    have eq := is_const_of_deriv_eq_zero (fun r => (dQ r).differentiableAt)
      (fun r => (dQ r).deriv) t s₀
    change C.tangentSupport t-5/6*C.k t*C.v t=_ at eq
    apply sub_eq_zero.mp
    simpa [Q,tangentSupport,hsx,hsy,hsk] using eq
  have dT (r : ℝ) : HasDerivAt (tang C) (I*(C.k r:ℂ)*tang C r) r := by
    convert! (C.dtx r).ofReal_comp.add ((C.dty r).ofReal_comp.mul_const I) using 1
    dsimp only [tang]
    push_cast
    linear_combination (C.k r:ℂ)*(C.ty r:ℂ)*I_sq
  have dB (r : ℝ) : HasDerivAt (stress C) (-(2/3:ℂ)*I*(C.k r:ℂ)*stress C r) r := by
    convert! (dv r).ofReal_comp.sub
      (((((C.dk r).ofReal_comp.pow 2).const_mul I)).div_const 3) using 1
    dsimp only [stress]
    push_cast
    linear_combination (2/9:ℂ)*(C.k r:ℂ)^3*I_sq
  let H (r : ℝ) := tang C r^2*stress C r^3
  have dH (r : ℝ) : HasDerivAt H 0 r := by
    convert! ((dT r).pow 2).mul ((dB r).pow 3) using 1
    simp only [Pi.pow_apply]
    ring
  have hi (t : ℝ) : tang C t^2*stress C t^3=tang C s₀^2*(b:ℂ)^3 := by
    have eq := is_const_of_deriv_eq_zero (fun r => (dH r).differentiableAt)
      (fun r => (dH r).deriv) t s₀
    simpa [H,stress,hsk,hsv] using eq
  have tnorm (t : ℝ) : normSq (tang C t)=1 := by
    simpa only [tang,normSq_add_mul_I] using C.unit t
  have zp (t : ℝ) : pos C t=(5/6:ℂ)*(C.k t:ℂ)*stress C t*tang C t := by
    have supp : pos C t = ((C.tangentSupport t:ℂ)+(C.normalSupport t:ℂ)*I)*tang C t := by
      apply Complex.ext
      · simp [pos,tang,tangentSupport,normalSupport,Complex.add_re,Complex.mul_re,Complex.mul_im]
        linear_combination -(C.x t)*(C.unit t)
      · simp [pos,tang,tangentSupport,normalSupport,Complex.add_im,Complex.mul_re,Complex.mul_im]
        linear_combination -(C.y t)*(C.unit t)
    rw [supp,qv t,pv t]
    dsimp only [stress]
    push_cast
    ring
  have radius (t : ℝ) : C.x t^2+C.y t^2=5/6*C.k t^2 := by
    have coords : C.x t^2+C.y t^2=C.normalSupport t^2+C.tangentSupport t^2 := by
      dsimp only [normalSupport,tangentSupport]
      linear_combination -(C.x t^2+C.y t^2)*(C.unit t)
    rw [coords,pv t,qv t]
    linear_combination (25/36*C.k t^2)*(en t)+(25/36*C.k t^2)*hb2
  intro t
  let B := stress C t
  let U := pos C t*conj (tang C s₀)
  have E : B*((C.v t:ℂ)+I*(C.k t:ℂ)^2/3)=(b:ℂ)^2 := by
    have e : (C.v t:ℂ)^2+(C.k t:ℂ)^4/9=(b:ℂ)^2 := by exact_mod_cast en t
    dsimp only [B,stress]
    linear_combination e-((C.k t:ℂ)^4/9)*I_sq
  have tu : tang C s₀*conj (tang C s₀)=1 := by rw [mul_conj,tnorm]; norm_num
  have rel : U^2*B=(25/36:ℂ)*(C.k t:ℂ)^2*(b:ℂ)^3 := by
    dsimp only [U,B]
    rw [zp t]
    calc
      _=(25/36:ℂ)*(C.k t:ℂ)^2*(tang C t^2*stress C t^3)*conj (tang C s₀)^2 := by ring
      _=(25/36:ℂ)*(C.k t:ℂ)^2*(b:ℂ)^3*(tang C s₀*conj (tang C s₀))^2 := by rw [hi]; ring
      _=_ := by rw [tu]; ring
  have hcomplex : U^2*(b:ℂ)^2=(25/36:ℂ)*(C.k t:ℂ)^2*(b:ℂ)^3*
      ((C.v t:ℂ)+I*(C.k t:ℂ)^2/3) := by
    linear_combination ((C.v t:ℂ)+I*(C.k t:ℂ)^2/3)*rel-U^2*E
  have im := congrArg Complex.im hcomplex
  let u := C.x t*C.tx s₀+C.y t*C.ty s₀
  let w := C.y t*C.tx s₀-C.x t*C.ty s₀
  have ur : U.re=u := by simp [U,u,pos,tang,Complex.mul_re]
  have ui : U.im=w := by simp [U,w,pos,tang,Complex.mul_im]; ring
  have imm : 2*u*w*b^2=25/108*C.k t^4*b^3 := by
    simp [pow_succ,Complex.mul_re,Complex.mul_im,ur,ui] at im
    linear_combination im
  change b*(C.x t^2+C.y t^2)^2=6*u*w
  rw [radius t]
  apply mul_right_cancel₀ (show b^2≠0 from pow_ne_zero 2 hb.ne')
  linear_combination -3*imm

theorem cubic_force_bernoulli_cartesian (C : ClosedUnitFrenetCurve) {ω a d j c : ℝ}
    (hp : ∀ s,C.positionForce s= -C.normalSupport s-ω*C.tangentSupport s)
    (hn : ¬∃ q, ∀s,C.positionCurvature s=q)
    (he : ∀ s,C.positionForce s=a*C.positionCurvature s^3+
      d*C.positionCurvature s^2+j*C.positionCurvature s+c) :
    ω=0 ∧ ∃ s₀,C.x s₀=0 ∧ C.y s₀=0 ∧ C.positionCurvature s₀=0 ∧
      ∀ t,Real.sqrt (6/5)*(C.x t^2+C.y t^2)^2=
      6*(C.x t*C.tx s₀+C.y t*C.ty s₀)*(C.y t*C.tx s₀-C.x t*C.ty s₀) := by
  obtain ⟨hω,ha,hd,hj,hc,s₀,hx,hy,hk,hv,_⟩ :=
    C.cubic_force_excludes_rotation_and_selects_bernoulli hp hn he
  subst ω a d j c
  refine ⟨rfl,s₀,hx,hy,hk,?_⟩
  rw [C.positionForce_eq,C.positionCurvature_eq] at he
  rw [C.positionForce_eq] at hp
  rw [C.positionCurvature_eq] at hk
  have d (t : ℝ) : HasDerivAt C.v (-2/9*C.k t^3) t := by
    have eq := he t
    dsimp [force] at eq
    convert C.dv t using 1
    linarith
  apply imaginary_quartic C (b:=Real.sqrt (6/5)) (Real.sqrt_pos.2 (by norm_num))
    (Real.sq_sqrt (by norm_num)) hx hy hk hv _ d
  intro t
  linarith [hp t,he t]

#print axioms cubic_force_bernoulli_cartesian
end ClosedSimilarity.ClosedUnitFrenetCurve
