import Lemniscate.BernoulliArclengthFrame
import Lemniscate.BernoulliProfileIdentification
import Lemniscate.PeriodicCoverExtension
import Lemniscate.BernoulliSobolevLinearization
import Lemniscate.BernoulliReferenceLength
import Lemniscate.PeriodicImmersionArclength
import Lemniscate.PeriodicCurveDilation

/-! The actual unit-speed Bernoulli reference on the spectral circle.
The auxiliary curve is sqrt(2) times the physical reference, so its
curvature is 3q/sqrt(2) and its tangential support is 2qp. The same
adjoint vector used by the physical normal-graph equation fixes its phase.

-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ContDiff ComplexConjugate

set_option maxHeartbeats 800000 in
theorem actual_bernoulli_reference_geometry (e : ℝ ≃o ℝ)
    (he : ∀ u, e u = ∫ t in (0:ℝ)..u, Real.sqrt 2*‖bernoulliVelocity t‖) :
    let β : ℝ → ℂ := fun x => (Real.sqrt 2:ℂ)*bernoulliCurve (e.symm x)
    let t : ℝ → ℂ := fun x =>
      bernoulliVelocity (e.symm x)/(‖bernoulliVelocity (e.symm x)‖:ℂ)
    let k : ℝ → ℝ := fun x => (3/Real.sqrt 2)*bernoulliProfileQ (e.symm x)
    let ks : ℝ → ℝ := fun x => (3/Real.sqrt 2)*bernoulliProfileP (e.symm x)
    ContDiff ℝ ∞ β ∧ Function.Periodic β (e (2*Real.pi)) ∧
      (∀ x, HasDerivAt β (t x) x ∧
        HasDerivAt t (I*(k x:ℂ)*t x) x ∧ HasDerivAt k (ks x) x ∧
        ‖t x‖=1 ∧ planarSignedCurvature β x=k x) ∧
      (∀ x, |k x|≤3 ∧ |ks x|≤3) := by
  let a : ℝ := Real.sqrt 2
  have ha : 0<a := Real.sqrt_pos.mpr (by norm_num)
  have ha0 : a≠0 := ha.ne'
  have ha1 : 1≤a := by
    dsimp only [a]
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by norm_num : (1:ℝ)≤2)
  have hvel : deriv bernoulliCurve=bernoulliVelocity :=
    funext fun u => (bernoulli_curve_geometry u).1.deriv
  obtain ⟨hcurve,hcurvePer,hregular⟩ := bernoulli_closed_expander
  obtain ⟨arc,hArc,_,_,_,_,hArcData⟩ :=
    periodic_immersion_arclength (2*Real.pi) (by positivity) bernoulliCurve
      hcurve hcurvePer (fun u => (hregular u).1)
  let L : ℝ := ∫ u in (0:ℝ)..(2*Real.pi), ‖deriv bernoulliCurve u‖
  let Γ : ℝ → ℂ := bernoulliCurve ∘ arc.symm
  let t₀ : ℝ → ℂ := fun s =>
    deriv bernoulliCurve (arc.symm s)/(‖deriv bernoulliCurve (arc.symm s)‖:ℂ)
  let k₀ : ℝ → ℝ := fun s => planarSignedCurvature bernoulliCurve (arc.symm s)
  change 0<L ∧ (∀ u, arc (u+2*Real.pi)=arc u+L) ∧
    ContDiff ℝ ∞ Γ ∧ Function.Periodic Γ L ∧
    ContDiff ℝ ∞ t₀ ∧ Function.Periodic t₀ L ∧
    ContDiff ℝ ∞ k₀ ∧ Function.Periodic k₀ L ∧ _ at hArcData
  obtain ⟨hL,_,hΓsmooth,hΓper,htsmooth,htper,hksmooth,hkper,hframe⟩ := hArcData
  have hcoordinate (u : ℝ) : e u=a*arc u := by
    rw [he,hArc,intervalIntegral.integral_const_mul,hvel]
  have hinverse (x : ℝ) : e.symm x=arc.symm (x/a) := by
    apply arc.injective
    rw [arc.apply_symm_apply]
    have hh := hcoordinate (e.symm x)
    rw [e.apply_symm_apply] at hh
    apply (eq_div_iff ha0).mpr
    simpa only [mul_comm] using hh.symm
  have hlength : a*L=e (2*Real.pi) := by
    calc
      a*L=a*arc (2*Real.pi) := congrArg (a*·) (hArc (2*Real.pi)).symm
      _=e (2*Real.pi) := (hcoordinate (2*Real.pi)).symm
  have hODE := bernoulli_arclength_profile_of_coordinate e he
  let β : ℝ → ℂ := fun x => (a:ℂ)*bernoulliCurve (e.symm x)
  let t : ℝ → ℂ := fun x =>
    bernoulliVelocity (e.symm x)/(‖bernoulliVelocity (e.symm x)‖:ℂ)
  let k : ℝ → ℝ := fun x => (3/a)*bernoulliProfileQ (e.symm x)
  let ks : ℝ → ℝ := fun x => (3/a)*bernoulliProfileP (e.symm x)
  have hβeq : (fun x => (a:ℂ)*Γ (x/a))=β := by
    funext x
    simp only [β,Γ,Function.comp_apply,hinverse]
  have hteq : (fun x => t₀ (x/a))=t := by
    funext x
    simp only [t₀,t,hvel,hinverse]
  have hkeq : (fun x => k₀ (x/a)/a)=k := by
    funext x
    dsimp only [k₀,k]
    rw [← hinverse,(hODE x).2.2.2]
    dsimp only [Function.comp_def]
    ring
  have hDil := periodic_curve_dilation a L ha hL
    (fun _ : Fin 2 => Γ) (fun _ : Fin 2 => t₀) (fun _ : Fin 2 => k₀)
    (fun _ => hΓsmooth) (fun _ => htsmooth) (fun _ => hksmooth)
    (fun _ => hΓper) (fun _ => htper) (fun _ => hkper)
    (fun _ s => (hframe s).1) (fun _ s => (hframe s).2.2.1)
    (fun _ s => (hframe s).2.1)
  have hd := hDil.2.1 0
  change ContDiff ℝ ∞ (fun x => (a:ℂ)*Γ (x/a)) ∧
    Function.Periodic (fun x => (a:ℂ)*Γ (x/a)) (a*L) ∧
    ContDiff ℝ ∞ (fun x => t₀ (x/a)) ∧
    Function.Periodic (fun x => t₀ (x/a)) (a*L) ∧
    ContDiff ℝ ∞ (fun x => k₀ (x/a)/a) ∧
    Function.Periodic (fun x => k₀ (x/a)/a) (a*L) ∧ _ at hd
  rw [hβeq,hteq,hkeq,hlength] at hd
  change ContDiff ℝ ∞ β ∧ Function.Periodic β (e (2*Real.pi)) ∧ _
  refine ⟨hd.1,hd.2.1,?_,?_⟩
  · intro x
    have hf := hd.2.2.2.2.2.2 x
    exact ⟨hf.1,hf.2.2.1,(hODE x).1.const_mul (3/a),hf.2.1,hf.2.2.2⟩
  · intro x
    let qx := bernoulliProfileQ (e.symm x)
    let px := bernoulliProfileP (e.symm x)
    have hfirst : 2*px^2+qx^4=1 := (hODE x).2.2.1
    have hq4 : (qx^2)^2≤(1:ℝ)^2 := by
      nlinarith only [hfirst,sq_nonneg px]
    have hq2 : qx^2≤1 := (sq_le_sq₀ (sq_nonneg qx) zero_le_one).mp hq4
    have hp2 : px^2≤1 := by
      nlinarith only [hfirst,sq_nonneg (qx^2)]
    have hq1 : |qx|≤1 := (sq_le_one_iff_abs_le_one qx).mp hq2
    have hp1 : |px|≤1 := (sq_le_one_iff_abs_le_one px).mp hp2
    have hc0 : 0≤3/a := by positivity
    have hc3 : 3/a≤3 := (div_le_iff₀ ha).mpr (by linarith only [ha1])
    constructor
    · change |(3/a)*qx|≤3
      rw [abs_mul,abs_of_nonneg hc0]
      exact (mul_le_of_le_one_right hc0 hq1).trans hc3
    · change |(3/a)*px|≤3
      rw [abs_mul,abs_of_nonneg hc0]
      exact (mul_le_of_le_one_right hc0 hp1).trans hc3

set_option maxHeartbeats 800000 in
/-- The actual Bernoulli reference on every spectral cover supplies the
unit-speed geometry and the same adjoint phase needed by the normalized
curvature-profile entry theorem. The displayed curvature is the auxiliary
geometric curvature; the evolution background retains physical curvature.
-/
theorem bernoulli_reference_normal_graph
    (e : ℝ ≃o ℝ)
    (he : ∀ u, e u = ∫ t in (0:ℝ)..u, Real.sqrt 2*‖bernoulliVelocity t‖)
    [Fact (0<e (2*Real.pi))]
    (q p : C(AddCircle (e (2*Real.pi)),ℂ))
    (hq : HasCircleDeriv (e (2*Real.pi)) q p)
    (hcurvature : ∀ x : ℝ, (planarSignedCurvature bernoulliCurve (e.symm x):ℂ)=
      3*q (x:AddCircle (e (2*Real.pi))))
    (M : ℕ) (S : ℝ) [Fact (0<S)] (hS : S=(M:ℝ)*e (2*Real.pi))
    (ψ : CircleL2 S)
    (hpair : inner ℂ ψ (circleContinuousL2 S
      (circleBernoulliBackground S
        (circlePeriodicExtension (e (2*Real.pi)) S M hS q)
        (circlePeriodicExtension (e (2*Real.pi)) S M hS p)).b)≠0) :
    let E := circlePeriodicExtension (e (2*Real.pi)) S M hS
    let Q := E q
    let P := E p
    let β : ℝ → ℂ := fun x => (Real.sqrt 2:ℂ)*bernoulliCurve (e.symm x)
    let t : ℝ → ℂ := fun x =>
      bernoulliVelocity (e.symm x)/(‖bernoulliVelocity (e.symm x)‖:ℂ)
    let k : ℝ → ℝ := fun x => (3/Real.sqrt 2)*bernoulliProfileQ (e.symm x)
    let ks : ℝ → ℝ := fun x => (3/Real.sqrt 2)*bernoulliProfileP (e.symm x)
    let b : C(AddCircle S,ℂ) := (2:ℂ) • (Q*P)
    S=(M:ℝ)*(4*Khalf) ∧
      ContDiff ℝ ∞ β ∧ Function.Periodic β S ∧
      (∀ x, HasDerivAt β (t x) x ∧ HasDerivAt t (I*(k x:ℂ)*t x) x ∧
        HasDerivAt k (ks x) x ∧ ‖t x‖=1 ∧ planarSignedCurvature β x=k x) ∧
      (∀ x, |k x|≤3 ∧ |ks x|≤3) ∧
      (∀ x : ℝ, b (x:AddCircle S)=((conj (t x)*β x).re:ℂ)) ∧
      b=((Real.sqrt 2:ℝ):ℂ) • (circleBernoulliBackground S Q P).b ∧
      inner ℂ ψ (circleContinuousL2 S b)≠0 := by
  let E := circlePeriodicExtension (e (2*Real.pi)) S M hS
  let Q := E q
  let P := E p
  let β : ℝ → ℂ := fun x => (Real.sqrt 2:ℂ)*bernoulliCurve (e.symm x)
  let t : ℝ → ℂ := fun x =>
    bernoulliVelocity (e.symm x)/(‖bernoulliVelocity (e.symm x)‖:ℂ)
  let k : ℝ → ℝ := fun x => (3/Real.sqrt 2)*bernoulliProfileQ (e.symm x)
  let ks : ℝ → ℝ := fun x => (3/Real.sqrt 2)*bernoulliProfileP (e.symm x)
  let b : C(AddCircle S,ℂ) := (2:ℂ) • (Q*P)
  have hroot : Real.sqrt (2:ℝ)≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hroot2 : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hrootC : ((Real.sqrt 2:ℝ):ℂ)^2=2 := by exact_mod_cast hroot2
  have hperiod : e (2*Real.pi)=4*Khalf := by
    rw [he,intervalIntegral.integral_const_mul,bernoulli_reference_length]
    field_simp [hroot] <;> ring
  obtain ⟨hβsmooth,hβperiod,hframe,hbounds⟩ := actual_bernoulli_reference_geometry e he
  have hβperiodS : Function.Periodic β S := by
    rw [hS]
    exact hβperiod.nat_mul M
  have hactual := bernoulli_circle_profile_identification e he q p hq hcurvature
  have hQ (x : ℝ) : Q (x:AddCircle S)=(bernoulliProfileQ (e.symm x):ℂ) :=
    (hactual x).1
  have hP (x : ℝ) : P (x:AddCircle S)=(bernoulliProfileP (e.symm x):ℂ) :=
    (hactual x).2
  have hbscale : b=((Real.sqrt 2:ℝ):ℂ) • (circleBernoulliBackground S Q P).b := by
    change (2:ℂ) • (Q*P)=((Real.sqrt 2:ℝ):ℂ) •
      (((Real.sqrt 2:ℝ):ℂ) • (Q*P))
    rw [smul_smul,← pow_two,hrootC]
  refine ⟨by rw [hS,hperiod],hβsmooth,hβperiodS,hframe,hbounds,?_,hbscale,?_⟩
  · intro x
    have hscale : Real.sqrt 2*(x/Real.sqrt 2)=x := by field_simp [hroot] <;> ring
    have hposition :=
      (bernoulli_arclength_frame e he (x/Real.sqrt 2)).2.2.2.2.2.2.2.2.1
    change conj (bernoulliVelocity (e.symm (Real.sqrt 2*(x/Real.sqrt 2)))/
        (‖bernoulliVelocity (e.symm (Real.sqrt 2*(x/Real.sqrt 2)))‖:ℂ))*
        bernoulliCurve (e.symm (Real.sqrt 2*(x/Real.sqrt 2))) =
      ((Real.sqrt 2*bernoulliProfileQ (e.symm (Real.sqrt 2*(x/Real.sqrt 2)))*
        bernoulliProfileP (e.symm (Real.sqrt 2*(x/Real.sqrt 2))):ℝ):ℂ)+
        ((-(bernoulliProfileQ (e.symm (Real.sqrt 2*(x/Real.sqrt 2))))^3:ℝ):ℂ)*I
        at hposition
    rw [hscale] at hposition
    have hsupport : (conj (t x)*β x).re=
        2*bernoulliProfileQ (e.symm x)*bernoulliProfileP (e.symm x) := by
      have hcomplex : conj (t x)*β x=((Real.sqrt 2:ℝ):ℂ)*
          (conj (t x)*bernoulliCurve (e.symm x)) := by dsimp only [β]; ring
      rw [hcomplex,hposition]
      simp only [Complex.mul_re,Complex.add_re,Complex.ofReal_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
        sub_zero,add_zero]
      calc
        _=(Real.sqrt 2)^2*bernoulliProfileQ (e.symm x)*
            bernoulliProfileP (e.symm x) := by ring
        _=_ := by rw [hroot2]
    rw [hsupport]
    change (2:ℂ)*(Q (x:AddCircle S)*P (x:AddCircle S))=
      ((2*bernoulliProfileQ (e.symm x)*bernoulliProfileP (e.symm x):ℝ):ℂ)
    rw [hQ,hP]
    push_cast
    ring
  · change inner ℂ ψ (circleContinuousL2 S b)≠0
    rw [hbscale,circle_continuous_l2_smul,inner_smul_right]
    apply mul_ne_zero
    · exact_mod_cast hroot
    · exact hpair

end Lemniscate
