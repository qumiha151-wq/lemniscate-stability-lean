import Lemniscate.BernoulliClassicalGraphEquation
import Lemniscate.NormalGraphContinuousFlow

/-! The actual Bernoulli rotation representative is shared by both
directions of the classical modulated equation. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

omit [Fact (0 < T)] in
private theorem bernoulli_rotation_coefficients
    (e : ℝ ≃o ℝ) (he : ∀ u, e u=∫ t in (0:ℝ)..u, Real.sqrt 2*‖bernoulliVelocity t‖)
    (q p : C(AddCircle T,ℂ))
    (hq : ∀ x : ℝ, q (x:AddCircle T)=(bernoulliProfileQ (e.symm x):ℂ))
    (hp : ∀ x : ℝ, p (x:AddCircle T)=(bernoulliProfileP (e.symm x):ℂ)) (s : ℝ) :
    let φ := fun s : ℝ => e.symm (Real.sqrt 2*s)
    let β := bernoulliCurve ∘ φ
    let t := fun s : ℝ => bernoulliVelocity (φ s)/(‖bernoulliVelocity (φ s)‖:ℂ)
    let K := circleBernoulliBackground T q p
    K.k ((Real.sqrt 2*s):AddCircle T)=((3*bernoulliProfileQ (φ s):ℝ):ℂ) ∧
      K.eta ((Real.sqrt 2*s):AddCircle T)=((conj (t s)*β s).im:ℂ) ∧
      K.b ((Real.sqrt 2*s):AddCircle T)=((conj (t s)*β s).re:ℂ) := by
  let φ := fun s : ℝ => e.symm (Real.sqrt 2*s)
  let β := bernoulliCurve ∘ φ
  let t := fun s : ℝ => bernoulliVelocity (φ s)/(‖bernoulliVelocity (φ s)‖:ℂ)
  have hpos := (bernoulli_arclength_frame e he s).2.2.2.2.2.2.2.2.1
  have hre : (conj (t s)*β s).re=
      Real.sqrt 2*bernoulliProfileQ (φ s)*bernoulliProfileP (φ s) := by
    simpa only [φ,β,t,Function.comp_def,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero] using congrArg Complex.re hpos
  have him : (conj (t s)*β s).im=-(bernoulliProfileQ (φ s))^3 := by
    simpa only [φ,β,t,Function.comp_def,Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,mul_one,zero_add,add_zero] using congrArg Complex.im hpos
  dsimp only
  rw [hre,him]
  simp only [circleBernoulliBackground,ContinuousMap.smul_apply,ContinuousMap.neg_apply,
    ContinuousMap.pow_apply,ContinuousMap.mul_apply,smul_eq_mul,hq,hp]
  dsimp only [φ]
  push_cast
  exact ⟨by ring,rfl,by ring⟩

set_option maxHeartbeats 800000 in
/-- The continuous representative of rotation has both its actual L2
value and its scalar geometric expression in the Bernoulli frame. -/
theorem bernoulli_classical_rotation_representation
    (e : ℝ ≃o ℝ) (he : ∀ u, e u=∫ t in (0:ℝ)..u, Real.sqrt 2*‖bernoulliVelocity t‖)
    (q p : C(AddCircle T,ℂ))
    (hq : ∀ x : ℝ, q (x:AddCircle T)=(bernoulliProfileQ (e.symm x):ℂ))
    (hp : ∀ x : ℝ, p (x:AddCircle T)=(bernoulliProfileP (e.symm x):ℂ))
    (g : CircleSobolevSpace T 2) (H : Fin 5 → C(AddCircle T,ℂ))
    (hreal : ∀ j x, ((H j x).re:ℂ)=H j x)
    (f : CircleSobolevSpace T 4)
    (hfg : circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)=g)
    (hjet : ∀ j : Fin 4, circleSobolevContinuousJet T f j=H j.castSucc)
    (hdomain : f ∈ circleNormalGraphDomain T (circleBernoulliBackground T q p)) :
    let φ := fun s : ℝ => e.symm (Real.sqrt 2*s)
    let β := bernoulliCurve ∘ φ
    let t := fun s : ℝ => bernoulliVelocity (φ s)/(‖bernoulliVelocity (φ s)‖:ℂ)
    let k := fun s : ℝ => 3*bernoulliProfileQ (φ s)
    let h := fun s : ℝ => (H 0 ((Real.sqrt 2*s):AddCircle T)).re
    let h₁ := fun s : ℝ => Real.sqrt 2*(H 1 ((Real.sqrt 2*s):AddCircle T)).re
    let G := circleNormalGraphContinuousRotation T (circleBernoulliBackground T q p) g
    circleContinuousL2 T G=circleNormalGraphRotationField T (circleBernoulliBackground T q p) g ∧
      ∀ s : ℝ, G ((Real.sqrt 2*s):AddCircle T)=
        (((conj (t s)*β s).re+((conj (t s)*β s).im+h s)*h₁ s/(1-k s*h s):ℝ):ℂ) := by
  dsimp only
  let φ := fun s : ℝ => e.symm (Real.sqrt 2*s)
  let β := bernoulliCurve ∘ φ
  let t := fun s : ℝ => bernoulliVelocity (φ s)/(‖bernoulliVelocity (φ s)‖:ℂ)
  let k := fun s : ℝ => 3*bernoulliProfileQ (φ s)
  let h := fun s : ℝ => (H 0 ((Real.sqrt 2*s):AddCircle T)).re
  let h₁ := fun s : ℝ => Real.sqrt 2*(H 1 ((Real.sqrt 2*s):AddCircle T)).re
  let K := circleBernoulliBackground T q p
  have hlow₀ : circleNormalGraphLowCoordinates T g 0=H 0 := by
    have hh := (circle_normal_graph_coordinates_low T f 0).symm
    rw [hfg,circle_normal_graph_coordinates] at hh
    simpa only [Matrix.cons_val_zero] using! hh.trans (hjet 0)
  have hlow₁ : circleNormalGraphLowCoordinates T g 1=((Real.sqrt 2:ℝ):ℂ) • H 1 := by
    have hh := (circle_normal_graph_coordinates_low T f 1).symm
    rw [hfg,circle_normal_graph_coordinates] at hh
    simpa only [Matrix.cons_val_one] using! hh.trans
      (congrArg (fun u : C(AddCircle T,ℂ) => ((Real.sqrt 2:ℝ):ℂ) • u) (hjet 1))
  have huA : IsUnit (1-K.k*circleNormalGraphLowCoordinates T g 0) := by
    have hh := (circle_normal_graph_domain_iff_low T K f).mp hdomain
    rw [hfg] at hh
    exact hh.1
  refine ⟨(circle_normal_graph_continuous_representatives T K (15/2)).2.1 g,?_⟩
  intro s
  have hKdata := bernoulli_rotation_coefficients T e he q p hq hp s
  have hk : K.k ((Real.sqrt 2*s):AddCircle T)=(k s:ℂ) := hKdata.1
  have hη : K.eta ((Real.sqrt 2*s):AddCircle T)=((conj (t s)*β s).im:ℂ) := hKdata.2.1
  have hb : K.b ((Real.sqrt 2*s):AddCircle T)=((conj (t s)*β s).re:ℂ) := hKdata.2.2
  have hh0 := hreal 0 ((Real.sqrt 2*s):AddCircle T)
  have hh1 := hreal 1 ((Real.sqrt 2*s):AddCircle T)
  change K.b ((Real.sqrt 2*s):AddCircle T)+
    (K.eta ((Real.sqrt 2*s):AddCircle T)+
      circleNormalGraphLowCoordinates T g 0 ((Real.sqrt 2*s):AddCircle T))*
    circleNormalGraphLowCoordinates T g 1 ((Real.sqrt 2*s):AddCircle T)*
    Ring.inverse (1-K.k*circleNormalGraphLowCoordinates T g 0)
      ((Real.sqrt 2*s):AddCircle T)=_
  rw [continuous_map_ring_inverse_apply _ huA]
  simp only [ContinuousMap.add_apply,ContinuousMap.mul_apply,ContinuousMap.sub_apply,
    ContinuousMap.one_apply,hlow₀,hlow₁,ContinuousMap.smul_apply,smul_eq_mul]
  rw [hk,hη,hb,← hh0,← hh1]
  push_cast
  simp only [div_eq_mul_inv,φ,β,t,k,Function.comp_def,Complex.ofReal_re,
    Complex.ofReal_mul,Complex.ofReal_ofNat]

set_option maxHeartbeats 800000 in
/-- An actual real scalar classical modulated height equation gives the
actual L2 normal-graph equation. Its geometric and rotation terms are
identified with their proved circle representatives. -/
theorem bernoulli_classical_modulation_converse
    (e : ℝ ≃o ℝ) (he : ∀ u, e u=∫ t in (0:ℝ)..u, Real.sqrt 2*‖bernoulliVelocity t‖)
    (q p : C(AddCircle T,ℂ))
    (hq : ∀ x : ℝ, q (x:AddCircle T)=(bernoulliProfileQ (e.symm x):ℂ))
    (hp : ∀ x : ℝ, p (x:AddCircle T)=(bernoulliProfileP (e.symm x):ℂ))
    (H : Fin 5 → C(AddCircle T,ℂ)) (hreal : ∀ j x, ((H j x).re:ℂ)=H j x)
    (hderiv : ∀ j : Fin 4, HasCircleDeriv T (H j.castSucc) (H j.succ))
    (f : CircleSobolevSpace T 4)
    (hjet : ∀ j : Fin 4, circleSobolevContinuousJet T f j=H j.castSucc)
    (hfourth : circleSobolevCoordinate T 4 4 f=circleContinuousL2 T (H 4))
    (hdomain : f ∈ circleNormalGraphDomain T (circleBernoulliBackground T q p))
    (hregular : ∀ x : ℝ,
      0<1-3*bernoulliProfileQ (e.symm x)*(H 0 (x:AddCircle T)).re)
    (V : C(AddCircle T,ℂ)) (hVreal : ∀ x, ((V x).re:ℂ)=V x) (ω : ℝ) :
    let φ := fun s : ℝ => e.symm (Real.sqrt 2*s)
    let β := bernoulliCurve ∘ φ
    let t := fun s : ℝ => bernoulliVelocity (φ s)/(‖bernoulliVelocity (φ s)‖:ℂ)
    let n := fun s : ℝ => I*t s
    let k := fun s : ℝ => 3*bernoulliProfileQ (φ s)
    let h := fun s : ℝ => (H 0 ((Real.sqrt 2*s):AddCircle T)).re
    let h₁ := fun s : ℝ => Real.sqrt 2*(H 1 ((Real.sqrt 2*s):AddCircle T)).re
    (∀ x : ℝ, (V (x:AddCircle T)).re+
      ω*((conj (t (x/Real.sqrt 2))*β (x/Real.sqrt 2)).re+
        ((conj (t (x/Real.sqrt 2))*β (x/Real.sqrt 2)).im+h (x/Real.sqrt 2))*
          h₁ (x/Real.sqrt 2)/(1-k (x/Real.sqrt 2)*h (x/Real.sqrt 2)))=
      normalGraphFlowRHS β n k h (15/2) (x/Real.sqrt 2)) →
    circleContinuousL2 T V+(ω:ℂ) • circleNormalGraphRotationField T
      (circleBernoulliBackground T q p)
      (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f))=
        circleNormalGraphFlow T (circleBernoulliBackground T q p) (15/2) f := by
  dsimp only
  intro hPDE
  let K := circleBernoulliBackground T q p
  let g := circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)
  let G := circleNormalGraphContinuousRotation T K g
  let Z := circleNormalGraphCoordinates T f
  let R := normalGraphRationalFlow K (15/2) ⟨Z 0,Z 1,Z 2,Z 3,(4:ℂ) • H 4⟩
  have hR := bernoulli_classical_graph_equation T e he q p hq hp H hreal hderiv
    f hjet hfourth hdomain hregular
  have hG := bernoulli_classical_rotation_representation T e he q p hq hp g H hreal f rfl hjet hdomain
  have hpoint : V+(ω:ℂ) • G=R := by
    apply ContinuousMap.ext
    intro x
    induction x using QuotientAddGroup.induction_on
    rename_i x
    let s := x/Real.sqrt 2
    have hroot : Real.sqrt (2:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    have hscale : Real.sqrt 2*s=x := by dsimp only [s]; field_simp [hroot]
    have hGp := (congrArg (fun y : ℝ => G (y:AddCircle T)) hscale.symm).trans (hG.2 s)
    change V (x:AddCircle T)+(ω:ℂ)*G (x:AddCircle T)=R (x:AddCircle T)
    rw [hGp,hR.2 x]
    simpa only [Complex.ofReal_add,Complex.ofReal_mul,hVreal] using congrArg Complex.ofReal (hPDE x)
  have hlinear : circleContinuousL2 T (V+(ω:ℂ) • G)=
      circleContinuousL2 T V+(ω:ℂ) • circleContinuousL2 T G := by
    simp only [circleContinuousL2,map_add,map_smul]
  exact (congrArg (fun z : CircleL2 T => circleContinuousL2 T V+(ω:ℂ) • z) hG.1.symm).trans
    (hlinear.symm.trans ((congrArg (circleContinuousL2 T) hpoint).trans hR.1.symm))

end Lemniscate

