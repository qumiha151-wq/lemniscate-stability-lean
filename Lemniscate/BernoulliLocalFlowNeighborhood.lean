import Lemniscate.BernoulliLocalFlowChartData
import Lemniscate.BernoulliLocalProfileNeighborhood
import Lemniscate.BernoulliReferenceNormalGraph
import Lemniscate.BernoulliClassicalModulationConverse
import Lemniscate.NormalizedCurveFamilyRegularity
import Lemniscate.PhysicalNormalizationDerivatives
import Lemniscate.PeriodicFamilyUniformNeighborhood
import Lemniscate.PeriodicSmoothClassicalJet
import Lemniscate.PeriodicCurvatureProfileEntry

/-! A small H2 normal graph gives an actual local normalized neighborhood
of a given smooth free elastic flow. All spatial proximity estimates use
only the first classical jet of the H2 height. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Set Filter CoarseArithmetic
open scoped ContDiff Topology ENNReal ComplexConjugate

private theorem flow_neighborhood_radius {P : ℝ → Prop} {Q : Prop}
    (h : ∃ r>0,P r) (k : ∀ r,0<r → P r → Q) : Q := by
  obtain ⟨r,hr,hP⟩ := h
  exact k r hr hP

private theorem flow_neighborhood_witness {E : Type*} {P : E → Prop} {Q : Prop}
    (h : ∃ x,P x) (k : ∀ x,P x → Q) : Q := by
  obtain ⟨x,hx⟩ := h
  exact k x hx

set_option maxHeartbeats 800000 in
private theorem smooth_real_height_lift
    (S : ℝ) [Fact (0<S)] (h : ℝ → ℝ)
    (hh : ContDiff ℝ ∞ h) (hp : Function.Periodic h S)
    (x₀ : CircleSobolevSpace S 2)
    (hvalue : ∀ x : ℝ,circleSobolevH1Embedding S (circleSobolevInclusion S 1 x₀)
      (x:AddCircle S)=(h x:ℂ)) :
    ∃ f : CircleSobolevSpace S 5,
      circleSobolevInclusion S 2 (circleSobolevInclusion S 3 (circleSobolevInclusion S 4 f))=x₀ ∧
      circleSobolevConjugation S 5 f=f ∧
      (∀ x : ℝ,circleSobolevClassicalJet S 4 f 0 (x:AddCircle S)=(h x:ℂ)) ∧
      ∀ x : ℝ,circleSobolevClassicalJet S 4 f 1 (x:AddCircle S)=((deriv h x:ℝ):ℂ) := by
  have hhC : ContDiff ℝ ∞ (fun x : ℝ => (h x:ℂ)) := Complex.ofRealCLM.contDiff.comp hh
  obtain ⟨F,hFpoint,hF⟩ := periodic_smooth_classical_jet S (fun x : ℝ => (h x:ℂ)) hhC
    (fun x => congrArg Complex.ofReal (hp x))
  let f : CircleSobolevSpace S 5 := ⟨WithLp.toLp 2
    (fun j : Fin 6 => circleContinuousL2 S (F j.val)),by
      apply (circle_sobolev_jet_mem_iff S 5 _).mpr
      intro j
      exact circle_classical_weak_deriv S (F j.val) (F (j.val+1)) (hF j.val)⟩
  have hf (j : Fin 6) : circleSobolevCoordinate S 5 j f=circleContinuousL2 S (F j.val) := rfl
  have hF₀ : F 0=circleSobolevH1Embedding S (circleSobolevInclusion S 1 x₀) := by
    ext x
    refine QuotientAddGroup.induction_on x ?_
    intro x
    simpa only [iteratedDeriv_zero,hvalue] using hFpoint 0 x
  have hfg : circleSobolevInclusion S 2
      (circleSobolevInclusion S 3 (circleSobolevInclusion S 4 f))=x₀ := by
    apply circle_sobolev_value_injective S 2
    change circleSobolevCoordinate S 5 0 f=circleSobolevCoordinate S 2 0 x₀
    rw [hf]
    simp only [Fin.val_zero,hF₀,circle_sobolev_h1_embedding_l2,
      circle_sobolev_inclusion_coordinate,Fin.castSucc_zero]
  have hFreal : star (F 0)=F 0 := by
    ext x
    refine QuotientAddGroup.induction_on x ?_
    intro x
    change conj (F 0 (x:AddCircle S))=F 0 (x:AddCircle S)
    rw [show F 0 (x:AddCircle S)=(h x:ℂ) by simpa only [iteratedDeriv_zero] using hFpoint 0 x]
    exact Complex.conj_ofReal _
  have hfreal : circleSobolevConjugation S 5 f=f := by
    apply circle_sobolev_value_injective S 5
    rw [circle_sobolev_conjugation_coordinate,hf,← circle_continuous_l2_star]
    simp only [Fin.val_zero,hFreal]
  have hzero : circleSobolevClassicalJet S 4 f 0=F 0 := by
    apply ContinuousMap.toLp_injective (p:=2) (𝕜:=ℂ) AddCircle.haarAddCircle
    change circleContinuousL2 S _=circleContinuousL2 S _
    rw [circle_sobolev_classical_jet_l2,hf]
    simp only [Fin.castSucc_zero,Fin.val_zero]
  have hz (x : ℝ) : circleSobolevClassicalJet S 4 f 0 (x:AddCircle S)=(h x:ℂ) := by
    rw [hzero]
    simpa only [iteratedDeriv_zero] using hFpoint 0 x
  refine ⟨f,hfg,hfreal,hz,?_⟩
  intro x
  have hder : HasDerivAt (fun y : ℝ => circleSobolevClassicalJet S 4 f 0 (y:AddCircle S))
      (circleSobolevClassicalJet S 4 f 1 (x:AddCircle S)) x := by
    simpa only [Fin.castSucc_zero,Fin.succ_zero_eq_one] using!
      circle_sobolev_classical_jet_deriv S 4 f (0:Fin 4) x
  have hfun : (fun y : ℝ => circleSobolevClassicalJet S 4 f 0 (y:AddCircle S))=
      fun y : ℝ => (h y:ℂ) := funext hz
  rw [hfun] at hder
  exact hder.unique ((hh.differentiable (by simp) x).hasDerivAt.ofReal_comp)

private theorem scaled_rotation_expression (a k h d : ℝ) (ha : a≠0) (z : ℂ) :
    (a:ℂ)*((z.re+(z.im+h)*(a*d)/(1-k*h):ℝ):ℂ)=
      (((((a:ℂ)*z).re+(((a:ℂ)*z).im+a*h)*(a*d)/(1-(k/a)*(a*h))):ℝ):ℂ) := by
  have hk : (k/a)*(a*h)=k*h := by field_simp [ha]
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,hk]
  push_cast
  simp only [div_eq_mul_inv]
  ring

set_option maxHeartbeats 800000 in
private theorem auxiliary_initial_rotation
    (S : ℝ) [Fact (0<S)] (e : ℝ ≃o ℝ)
    (he : ∀ u,e u=∫ t in (0:ℝ)..u,Real.sqrt 2*‖bernoulliVelocity t‖)
    (q p : C(AddCircle S,ℂ))
    (hq : ∀ x : ℝ,q (x:AddCircle S)=(bernoulliProfileQ (e.symm x):ℂ))
    (hp : ∀ x : ℝ,p (x:AddCircle S)=(bernoulliProfileP (e.symm x):ℂ))
    (ψ : CircleL2 S) (hψ : circleConjugate S ψ=ψ) (η : ℝ)
    (hdomain : ∀ f : CircleSobolevSpace S 4,
      ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)‖<η →
        f∈circleNormalGraphDomain S (circleBernoulliBackground S q p))
    (hden : ∀ g : CircleSobolevSpace S 2,‖g‖<η →
      circleNormalGraphRotationFunctional S ψ
        (circleNormalGraphRotationField S (circleBernoulliBackground S q p) g)≠0)
    (h₀ : ℝ → ℝ) (hh₀ : ContDiff ℝ ∞ h₀) (hp₀ : Function.Periodic h₀ S)
    (x₀ : CircleSobolevSpace S 2) (hx₀ : ‖x₀‖<η)
    (hvalue : ∀ x : ℝ,circleSobolevH1Embedding S (circleSobolevInclusion S 1 x₀)
      (x:AddCircle S)=(h₀ x:ℂ)) :
    ∃ G : C(AddCircle S,ℂ),
      (∀ x : ℝ,G (x:AddCircle S)=
        (((conj (bernoulliAuxiliaryTangent e x)*bernoulliAuxiliaryCurve e x).re+
          ((conj (bernoulliAuxiliaryTangent e x)*bernoulliAuxiliaryCurve e x).im+Real.sqrt 2*h₀ x)*
            deriv (fun s => Real.sqrt 2*h₀ s) x/
              (1-bernoulliAuxiliaryCurvature e x*(Real.sqrt 2*h₀ x)):ℝ):ℂ)) ∧
      (inner ℂ ψ (circleContinuousL2 S G)).re≠0 := by
  obtain ⟨f,hfg,hfreal,hzero,hone⟩ := smooth_real_height_lift S h₀ hh₀ hp₀ x₀ hvalue
  let H := circleSobolevClassicalJet S 4 f
  have hreal (j : Fin 5) (x : AddCircle S) : ((H j x).re:ℂ)=H j x := by
    have hs := circle_sobolev_classical_jet_conjugation S 4 f j
    rw [hfreal] at hs
    exact Complex.conj_eq_iff_re.mp (congrArg (fun F : C(AddCircle S,ℂ) => F x) hs.symm)
  have hjet (j : Fin 4) : circleSobolevContinuousJet S (circleSobolevInclusion S 4 f) j=
      H j.castSucc := by
    apply ContinuousMap.toLp_injective (p:=2) (𝕜:=ℂ) AddCircle.haarAddCircle
    change circleContinuousL2 S _=circleContinuousL2 S _
    rw [(circle_sobolev_classical_jet_l2 S 3),circle_sobolev_classical_jet_l2]
    rfl
  have hRot := bernoulli_classical_rotation_representation S e he q p hq hp x₀ H hreal
    (circleSobolevInclusion S 4 f) hfg hjet (hdomain _ (by rw [hfg]; exact hx₀))
  let K := circleBernoulliBackground S q p
  let R := circleNormalGraphContinuousRotation S K x₀
  let G : C(AddCircle S,ℂ) := (Real.sqrt 2:ℂ) • R
  have hsqrt : Real.sqrt (2:ℝ)≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hscale (x : ℝ) : Real.sqrt 2*(x/Real.sqrt 2)=x := by field_simp [hsqrt]
  have hR (x : ℝ) : R (x:AddCircle S)=
      (((conj (bernoulliAuxiliaryTangent e x)*bernoulliCurve (e.symm x)).re+
        ((conj (bernoulliAuxiliaryTangent e x)*bernoulliCurve (e.symm x)).im+h₀ x)*
          (Real.sqrt 2*deriv h₀ x)/(1-(3*bernoulliProfileQ (e.symm x))*h₀ x):ℝ):ℂ) := by
    simpa only [H,hscale,hzero,hone,Complex.ofReal_re,Function.comp_def,
      bernoulliAuxiliaryTangent] using! hRot.2 (x/Real.sqrt 2)
  have hG (x : ℝ) : G (x:AddCircle S)=
      (((conj (bernoulliAuxiliaryTangent e x)*bernoulliAuxiliaryCurve e x).re+
        ((conj (bernoulliAuxiliaryTangent e x)*bernoulliAuxiliaryCurve e x).im+Real.sqrt 2*h₀ x)*
          deriv (fun s => Real.sqrt 2*h₀ s) x/
            (1-bernoulliAuxiliaryCurvature e x*(Real.sqrt 2*h₀ x)):ℝ):ℂ) := by
    change (Real.sqrt 2:ℂ)*R (x:AddCircle S)=_
    rw [hR]
    have hd : deriv (fun s => Real.sqrt 2*h₀ s) x=Real.sqrt 2*deriv h₀ x :=
      ((hh₀.differentiable (by simp) x).hasDerivAt.const_mul (Real.sqrt 2)).deriv
    have hk : bernoulliAuxiliaryCurvature e x=(3*bernoulliProfileQ (e.symm x))/Real.sqrt 2 := by
      dsimp only [bernoulliAuxiliaryCurvature]
      ring
    have hb : conj (bernoulliAuxiliaryTangent e x)*bernoulliAuxiliaryCurve e x=
        (Real.sqrt 2:ℂ)*(conj (bernoulliAuxiliaryTangent e x)*bernoulliCurve (e.symm x)) := by
      dsimp only [bernoulliAuxiliaryCurve]
      ring
    rw [hd,hk,hb]
    exact scaled_rotation_expression (Real.sqrt 2) (3*bernoulliProfileQ (e.symm x))
      (h₀ x) (deriv h₀ x) hsqrt _
  have hGreal : star G=G := by
    ext x
    refine QuotientAddGroup.induction_on x ?_
    intro x
    change conj (G (x:AddCircle S))=G (x:AddCircle S)
    rw [hG]
    exact Complex.conj_ofReal _
  have hGl2real : circleConjugate S (circleContinuousL2 S G)=circleContinuousL2 S G := by
    rw [← circle_continuous_l2_star,hGreal]
  have hPair : inner ℂ ψ (circleContinuousL2 S G)≠0 := by
    change inner ℂ ψ (circleContinuousL2 S ((Real.sqrt 2:ℂ) • R))≠0
    rw [circle_continuous_l2_smul,hRot.1,inner_smul_right]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hsqrt) (hden x₀ hx₀)
  refine ⟨G,hG,?_⟩
  intro hz
  apply hPair
  apply Complex.ext
  · exact hz
  · exact circle_inner_im_eq_zero_of_real S ψ _ hψ hGl2real

private abbrev flowNeighborhoodHeightRadius (S : ℝ) [Fact (0<S)] : ℝ :=
  (1/100:ℝ)/(2*(Real.sqrt 2*4*(‖circleSobolevClassicalJet S 1‖+1)))

set_option maxHeartbeats 800000 in
private theorem flow_neighborhood_box
    (S : ℝ) [Fact (0<S)] (β T : ℝ → ℂ) (κ h₀ : ℝ → ℝ)
    (hβ : ∀ x,HasDerivAt β (T x) x)
    (hT : ∀ x,HasDerivAt T (I*(κ x:ℂ)*T x) x)
    (hunit : ∀ x,‖T x‖=1) (hκ : ∀ x,|κ x|≤3)
    (hh₀ : ContDiff ℝ ∞ h₀) (x₀ : CircleSobolevSpace S 2)
    (hvalue : ∀ x : ℝ,circleSobolevH1Embedding S (circleSobolevInclusion S 1 x₀)
      (x:AddCircle S)=(h₀ x:ℂ)) (hx₀ : ‖x₀‖<flowNeighborhoodHeightRadius S)
    (Γ V : (ℝ × ℝ) × ℝ → ℂ)
    (hΓc : ContinuousOn Γ ((Ici (0:ℝ) ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℝ)))
    (hVc : ContinuousOn V ((Ici (0:ℝ) ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℝ)))
    (hd : ∀ q ∈ Ici (0:ℝ) ×ˢ (univ : Set ℝ),∀ x,
      HasDerivAt (fun s => Γ (q,s)) (V (q,x)) x)
    (hΓper : ∀ q ∈ Ici (0:ℝ) ×ˢ (univ : Set ℝ),Function.Periodic (fun x => Γ (q,x)) S)
    (hVper : ∀ q ∈ Ici (0:ℝ) ×ˢ (univ : Set ℝ),Function.Periodic (fun x => V (q,x)) S)
    (hbase : ∀ x,Γ ((0,0),x)=β x+I*((Real.sqrt 2*h₀ x:ℝ):ℂ)*T x) :
    ∃ r>0,∀ q ∈ insert ((0:ℝ),0) (Ioo 0 r ×ˢ Ioo (-r) r),∀ x,
      ‖Γ (q,x)-β x‖≤1/100 ∧ ‖V (q,x)-T x‖≤1/100 ∧ ‖V (q,x)‖≤1+1/100 := by
  let J := circleSobolevClassicalJet S 1 x₀
  let Cop := ‖circleSobolevClassicalJet S 1‖
  let C := Real.sqrt 2*4*(Cop+1)
  have hC : 0<C := by dsimp only [C,Cop]; positivity
  have hzero : J 0=circleSobolevH1Embedding S (circleSobolevInclusion S 1 x₀) := by
    apply ContinuousMap.toLp_injective (p:=2) (𝕜:=ℂ) AddCircle.haarAddCircle
    change circleContinuousL2 S _=circleContinuousL2 S _
    rw [circle_sobolev_classical_jet_l2,circle_sobolev_h1_embedding_l2]
    simp only [circle_sobolev_inclusion_coordinate]
  have hz (x : ℝ) : J 0 (x:AddCircle S)=(h₀ x:ℂ) := by rw [hzero,hvalue]
  have hone (x : ℝ) : J 1 (x:AddCircle S)=((deriv h₀ x:ℝ):ℂ) := by
    have hd₀ := circle_sobolev_classical_jet_deriv S 1 x₀ (0:Fin 1) x
    have hfun : (fun y : ℝ => J 0 (y:AddCircle S))=(fun y : ℝ => (h₀ y:ℂ)) := funext hz
    change HasDerivAt (fun y : ℝ => J 0 (y:AddCircle S)) (J 1 (x:AddCircle S)) x at hd₀
    rw [hfun] at hd₀
    exact hd₀.unique ((hh₀.differentiable (by simp) x).hasDerivAt.ofReal_comp)
  have hcoord (j : Fin 2) (x : ℝ) : ‖J j (x:AddCircle S)‖≤Cop*‖x₀‖ :=
    ((J j).norm_coe_le_norm _).trans
      ((norm_le_pi_norm J j).trans ((circleSobolevClassicalJet S 1).le_opNorm x₀))
  have h₀bound (x : ℝ) : |h₀ x|≤Cop*‖x₀‖ := by
    simpa only [hz,Complex.norm_real,Real.norm_eq_abs] using hcoord 0 x
  have h₁bound (x : ℝ) : |deriv h₀ x|≤Cop*‖x₀‖ := by
    simpa only [hone,Complex.norm_real,Real.norm_eq_abs] using hcoord 1 x
  have hCX : C*‖x₀‖<(1/100:ℝ)/2 := by
    have hh : ‖x₀‖<(1/100:ℝ)/(2*C) := hx₀
    have hs := (lt_div_iff₀ (by positivity : 0<2*C)).mp hh
    nlinarith
  have hposition (x : ℝ) : ‖Γ ((0,0),x)-β x‖≤(1/100:ℝ)/2 := by
    rw [hbase,add_sub_cancel_left,norm_mul,norm_mul,Complex.norm_I,hunit,mul_one,one_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.sqrt_nonneg 2)]
    have hCop : 0≤Cop := by
      change (0:ℝ)≤‖circleSobolevClassicalJet S 1‖
      exact (circleSobolevClassicalJet S 1).opNorm_nonneg
    calc
      Real.sqrt 2*|h₀ x|≤Real.sqrt 2*(Cop*‖x₀‖) :=
        mul_le_mul_of_nonneg_left (h₀bound x) (Real.sqrt_nonneg 2)
      _≤C*‖x₀‖ := by
        dsimp only [C]
        nlinarith [mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg x₀),
          mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hCop) (norm_nonneg x₀)]
      _≤(1/100:ℝ)/2 := hCX.le
  have hvelocity (x : ℝ) : V ((0,0),x)=
      T x+I*((Real.sqrt 2*deriv h₀ x:ℝ):ℂ)*T x+
        I*((Real.sqrt 2*h₀ x:ℝ):ℂ)*(I*(κ x:ℂ)*T x) := by
    have dh := ((hh₀.differentiable (by simp) x).hasDerivAt.const_mul (Real.sqrt 2)).ofReal_comp
    have dg := (hβ x).add ((dh.const_mul I).mul (hT x))
    have hf : (fun y : ℝ => Γ ((0,0),y))=
        fun y => β y+I*((Real.sqrt 2*h₀ y:ℝ):ℂ)*T y := funext hbase
    have dv := hd (0,0) (by simp) x
    rw [hf] at dv
    have he := dv.unique dg
    simpa only [add_assoc,add_left_comm,add_comm] using he
  have htangent (x : ℝ) : ‖V ((0,0),x)-T x‖≤(1/100:ℝ)/2 := by
    have hv : V ((0,0),x)-T x=I*((Real.sqrt 2*deriv h₀ x:ℝ):ℂ)*T x+
        I*((Real.sqrt 2*h₀ x:ℝ):ℂ)*(I*(κ x:ℂ)*T x) := by rw [hvelocity]; ring
    rw [hv]
    have hnorm₁ : ‖I*((Real.sqrt 2*deriv h₀ x:ℝ):ℂ)*T x‖=Real.sqrt 2*|deriv h₀ x| := by
      simp only [norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,hunit,
        one_mul,mul_one,abs_of_nonneg (Real.sqrt_nonneg 2)]
    have hnorm₀ : ‖I*((Real.sqrt 2*h₀ x:ℝ):ℂ)*(I*(κ x:ℂ)*T x)‖=
         Real.sqrt 2 * |h₀ x| * |κ x| := by
      simp only [norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,hunit,
        one_mul,mul_one,abs_of_nonneg (Real.sqrt_nonneg 2)]
    have hCop : 0≤Cop := by
      change (0:ℝ)≤‖circleSobolevClassicalJet S 1‖
      exact (circleSobolevClassicalJet S 1).opNorm_nonneg
    calc
      _≤Real.sqrt 2 * |deriv h₀ x|+Real.sqrt 2 * |h₀ x| * |κ x| := by
        simpa only [hnorm₁,hnorm₀] using norm_add_le
          (I*((Real.sqrt 2*deriv h₀ x:ℝ):ℂ)*T x)
          (I*((Real.sqrt 2*h₀ x:ℝ):ℂ)*(I*(κ x:ℂ)*T x))
      _≤Real.sqrt 2*(Cop*‖x₀‖)+Real.sqrt 2*(Cop*‖x₀‖)*3 := by
        exact add_le_add (mul_le_mul_of_nonneg_left (h₁bound x) (Real.sqrt_nonneg 2))
          (mul_le_mul (mul_le_mul_of_nonneg_left (h₀bound x) (Real.sqrt_nonneg 2)) (hκ x)
            (abs_nonneg _) (by positivity))
      _≤C*‖x₀‖ := by
        dsimp only [C]
        nlinarith [mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg x₀)]
      _≤(1/100:ℝ)/2 := hCX.le
  obtain ⟨r,hr,hclose⟩ := periodic_family_uniform_neighborhood
    (Ici (0:ℝ) ×ˢ (univ : Set ℝ)) (0,0) (by simp) Γ V hΓc hVc S
    (Fact.out : 0<S) hΓper hVper β T (1/100) (by norm_num) hposition htangent
  refine ⟨r/2,half_pos hr,?_⟩
  intro q hq x
  have hqC : q∈Ici (0:ℝ) ×ˢ (univ : Set ℝ) := by
    rcases hq with rfl|hq
    · simp
    · exact ⟨hq.1.1.le,mem_univ _⟩
  have hdist : dist q ((0:ℝ),0)<r := by
    rcases hq with rfl|hq
    · simpa only [dist_self] using hr
    · rw [Prod.dist_eq]
      apply max_lt_iff.mpr
      exact ⟨by simpa only [Real.dist_eq,sub_zero,abs_of_pos hq.1.1] using
        hq.1.2.trans (half_lt_self hr),
        by simpa only [Real.dist_eq,sub_zero] using
          ((abs_lt.mpr hq.2).trans (half_lt_self hr))⟩
  have hp := hclose q hqC hdist x
  refine ⟨hp.1.le,hp.2.le,?_⟩
  calc
    ‖V (q,x)‖≤‖V (q,x)-T x‖+‖T x‖ := by
      simpa only [sub_add_cancel] using norm_add_le (V (q,x)-T x) (T x)
    _≤1+1/100 := by rw [hunit]; linarith only [hp.2]

set_option maxHeartbeats 800000 in
private theorem normalized_flow_family
    (S : ℝ) [Fact (0<S)] (a : ℝ) (ha : 0<a) (σ₀ α₀ : ℝ) (hσ₀ : 0≤σ₀)
    (ρ : ℝ → ℝ) (hρ : ∀ t : ℝ,0≤t → ρ t=(a^4+30*t)^(1/4:ℝ)) (p₀ : ℂ)
    (P : ℝ) (χ₀ : ℝ ≃o ℝ) (hχ : ContDiff ℝ ∞ (χ₀ : ℝ → ℝ))
    (hdeck : ∀ x,χ₀ (x+S/Real.sqrt 2)=χ₀ x+P)
    (Y : ℝ → ℝ → ℂ)
    (hY : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => Y z.1 z.2)
      (Ici (0:ℝ) ×ˢ (univ : Set ℝ)))
    (hYper : ∀ t : ℝ,0≤t → Function.Periodic (Y t) P) :
    ∃ Γ V : (ℝ × ℝ) × ℝ → ℂ,
      ContDiffOn ℝ ∞ Γ ((Ici (0:ℝ) ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℝ)) ∧
      ContDiffOn ℝ ∞ V ((Ici (0:ℝ) ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℝ)) ∧
      (∀ q ∈ Ici (0:ℝ) ×ˢ (univ : Set ℝ),∀ x,
        HasDerivAt (fun s => Γ (q,s)) (V (q,x)) x) ∧
      (∀ q ∈ Ici (0:ℝ) ×ˢ (univ : Set ℝ),Function.Periodic (fun x => Γ (q,x)) S) ∧
      (∀ q ∈ Ici (0:ℝ) ×ˢ (univ : Set ℝ),Function.Periodic (fun x => V (q,x)) S) ∧
      ∀ q ∈ Ici (0:ℝ) ×ˢ (univ : Set ℝ),∀ x,
        Γ (q,x)=(Real.sqrt 2:ℂ)*Complex.exp (((-(α₀+q.2):ℝ):ℂ)*I)*
          (Y (physicalTime a (σ₀+q.1)) (χ₀ (x/Real.sqrt 2))-p₀)/
            (ρ (physicalTime a (σ₀+q.1)):ℂ) := by
  let C := Ici (0:ℝ) ×ˢ (univ : Set ℝ)
  let A := C ×ˢ (univ : Set ℝ)
  let X := fun z : ℝ × ℝ => (ρ (physicalTime a z.1):ℂ)⁻¹*
    (Y (physicalTime a z.1) z.2-p₀)
  have hX : ContDiffOn ℝ ∞ X (Ici (0:ℝ) ×ˢ (univ : Set ℝ)) :=
    (normalized_curve_family_regularity a ha ρ hρ (fun z : ℝ × ℝ => Y z.1 z.2) hY p₀).1
  let F := fun z : (ℝ × ℝ) × ℝ => (σ₀+z.1.1,χ₀ (z.2/Real.sqrt 2))
  have hF : ContDiff ℝ ∞ F :=
    (contDiff_const.add contDiff_fst.fst).prodMk (hχ.comp (contDiff_snd.div_const (Real.sqrt 2)))
  have hmap : MapsTo F A (Ici (0:ℝ) ×ˢ (univ : Set ℝ)) :=
    fun z hz => ⟨add_nonneg hσ₀ hz.1.1,mem_univ _⟩
  let E := fun z : (ℝ × ℝ) × ℝ => Complex.exp (((-(α₀+z.1.2):ℝ):ℂ)*I)
  have hθ : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => -(α₀+z.1.2)) :=
    (contDiff_const.add contDiff_fst.snd).neg
  have hθC : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => ((-(α₀+z.1.2):ℝ):ℂ)) :=
    (Complex.ofRealCLM.contDiff : ContDiff ℝ ∞ (fun x : ℝ => (x:ℂ))).comp hθ
  have hE : ContDiff ℝ ∞ E := by
    simpa only [E] using! (hθC.mul
      (contDiff_const : ContDiff ℝ ∞ (fun _ : (ℝ × ℝ) × ℝ => (I:ℂ)))).cexp
  let Γ := fun z : (ℝ × ℝ) × ℝ => (Real.sqrt 2:ℂ)*E z*X (F z)
  have hΓ : ContDiffOn ℝ ∞ Γ A :=
    (contDiffOn_const.mul hE.contDiffOn).mul (hX.comp hF.contDiffOn hmap)
  have hC : UniqueDiffOn ℝ C := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hSpatial := spatial_derivative_within_smooth C univ hC isOpen_univ Γ hΓ
  let V := fun z : (ℝ × ℝ) × ℝ => spatialDerivativeWithin C univ Γ z (1:ℝ)
  have hV : ContDiffOn ℝ ∞ V A := by
    simpa only [V] using hSpatial.1.clm_apply
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : (ℝ × ℝ) × ℝ => (1:ℝ)) A)
  have hd (q : ℝ × ℝ) (hq : q∈C) (x : ℝ) :
      HasDerivAt (fun s => Γ (q,s)) (V (q,x)) x :=
    (hSpatial.2 q hq x (mem_univ _)).hasDerivAt
  have hΓper (q : ℝ × ℝ) (hq : q∈C) : Function.Periodic (fun x => Γ (q,x)) S := by
    intro x
    have ht : 0≤physicalTime a (σ₀+q.1) :=
      ((physical_time_inverse a ha).2.1 (σ₀+q.1)).2.2.1 (add_nonneg hσ₀ hq.1)
    have hshift : χ₀ ((x+S)/Real.sqrt 2)=χ₀ (x/Real.sqrt 2)+P := by
      rw [show (x+S)/Real.sqrt 2=x/Real.sqrt 2+S/Real.sqrt 2 by ring,hdeck]
    dsimp only [Γ,E,X,F]
    rw [hshift,hYper _ ht]
  have hVper (q : ℝ × ℝ) (hq : q∈C) : Function.Periodic (fun x => V (q,x)) S := by
    intro x
    have hshift : HasDerivAt (fun y : ℝ => Γ (q,y+S)) (V (q,x+S)) x := by
      simpa only [Function.comp_def,one_smul] using!
        (hd q hq (x+S)).scomp x ((hasDerivAt_id x).add_const S)
    have heq : (fun y : ℝ => Γ (q,y+S))=(fun y : ℝ => Γ (q,y)) := funext (hΓper q hq)
    rw [heq] at hshift
    exact hshift.unique (hd q hq x)
  refine ⟨Γ,V,hΓ,hV,hd,hΓper,hVper,?_⟩
  intro q hq x
  dsimp only [Γ,E,X,F]
  simp only [div_eq_mul_inv]
  ring

private abbrev AuxiliaryReferenceData (S : ℝ) (e : ℝ ≃o ℝ) : Prop :=
  ContDiff ℝ ∞ (bernoulliAuxiliaryCurve e) ∧ Function.Periodic (bernoulliAuxiliaryCurve e) S ∧
  ContDiff ℝ ∞ (bernoulliAuxiliaryTangent e) ∧ Function.Periodic (bernoulliAuxiliaryTangent e) S ∧
  ContDiff ℝ ∞ (bernoulliAuxiliaryCurvature e) ∧ Function.Periodic (bernoulliAuxiliaryCurvature e) S ∧
  ∀ x,HasDerivAt (bernoulliAuxiliaryCurve e) (bernoulliAuxiliaryTangent e x) x ∧
    HasDerivAt (bernoulliAuxiliaryTangent e)
      (I*(bernoulliAuxiliaryCurvature e x:ℂ)*bernoulliAuxiliaryTangent e x) x ∧
    ‖bernoulliAuxiliaryTangent e x‖=1 ∧ |bernoulliAuxiliaryCurvature e x|≤3

set_option maxHeartbeats 800000 in
private theorem auxiliary_reference_data
    (T S : ℝ) [Fact (0<T)] [Fact (0<S)] (e : ℝ ≃o ℝ)
    (he : ∀ u,e u=∫ t in (0:ℝ)..u,Real.sqrt 2*‖bernoulliVelocity t‖)
    (hT : T=e (2*Real.pi)) (q p : C(AddCircle T,ℂ)) (hq : HasCircleDeriv T q p)
    (hqlift : ∀ x : ℝ,q (x:AddCircle T)=(bernoulliProfileQ (e.symm x):ℂ))
    (M : ℕ) (hS : S=(M:ℝ)*T) (ψ : CircleL2 S)
    (hpair : inner ℂ ψ (circleContinuousL2 S
      (circleBernoulliBackground S (circlePeriodicExtension T S M hS q)
        (circlePeriodicExtension T S M hS p)).b)≠0) : AuxiliaryReferenceData S e := by
  subst T
  have hcurvature (x : ℝ) : (planarSignedCurvature bernoulliCurve (e.symm x):ℂ)=
      3*q (x:AddCircle (e (2*Real.pi))) := by
    rw [(bernoulli_arclength_profile_of_coordinate e he x).2.2.2,hqlift]
    simp only [Function.comp_apply,Complex.ofReal_mul,Complex.ofReal_ofNat]
  obtain ⟨_,hβ,hβper,hframe,hbounds,_,_,_⟩ :=
    bernoulli_reference_normal_graph e he q p hq hcurvature M S hS ψ hpair
  let β := bernoulliAuxiliaryCurve e
  let t := bernoulliAuxiliaryTangent e
  let k := bernoulliAuxiliaryCurvature e
  have hdβ : deriv β=t := funext fun x => (hframe x).1.deriv
  have hts : ContDiff ℝ ∞ t := by
    rw [← hdβ]
    exact (contDiff_infty_iff_deriv.mp hβ).2
  have htp : Function.Periodic t S := by
    have hh := periodic_iterated_deriv S β hβper 1
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,hdβ] using hh
  have hdtp : Function.Periodic (deriv t) S := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using periodic_iterated_deriv S t htp 1
  have hk (x : ℝ) : k x=(conj (t x)*deriv t x).im := by
    have hc : planarSignedCurvature β x=k x := by
      simpa only [β,k,bernoulliAuxiliaryCurve,bernoulliAuxiliaryCurvature] using
        (hframe x).2.2.2.2
    rw [← hc]
    change (conj (deriv β x)*deriv (deriv β) x).im/‖deriv β x‖^3=
      (conj (t x)*deriv t x).im
    have hu : ‖t x‖=1 := (hframe x).2.2.2.1
    rw [hdβ,hu]
    simp only [one_pow,div_one]
  have hks : ContDiff ℝ ∞ k := by
    rw [funext hk]
    exact Complex.imCLM.contDiff.comp ((Complex.conjCLE.contDiff.comp hts).mul
      (contDiff_infty_iff_deriv.mp hts).2)
  have hkp : Function.Periodic k S := by
    intro x
    rw [hk (x+S),hk x,htp x,hdtp x]
  exact ⟨hβ,hβper,hts,htp,hks,hkp,fun x =>
    ⟨(hframe x).1,(hframe x).2.1,(hframe x).2.2.2.1,(hbounds x).1⟩⟩

private theorem undo_base_rotation (c α : ℝ) (r p b t : ℂ) (h : ℝ) (hr : r≠0) :
    (c:ℂ)*Complex.exp (((-α:ℝ):ℂ)*I)*
      (p+r*(Complex.exp ((α:ℂ)*I)*(b+(h:ℂ)*(I*t)))-p)/r=
        (c:ℂ)*b+I*((c*h:ℝ):ℂ)*t := by
  have hexp : Complex.exp (((-α:ℝ):ℂ)*I)*Complex.exp ((α:ℂ)*I)=1 := by
    rw [← Complex.exp_add]
    have hz : ((-α:ℝ):ℂ)*I+(α:ℂ)*I=0 := by push_cast; ring
    rw [hz,Complex.exp_zero]
  calc
    _=(c:ℂ)*(Complex.exp (((-α:ℝ):ℂ)*I)*Complex.exp ((α:ℂ)*I))*(b+(h:ℂ)*(I*t)) := by
      field_simp [hr] <;> ring
    _=_ := by rw [hexp]; push_cast; ring

set_option maxHeartbeats 1000000 in
private theorem actual_flow_neighborhood
    (S : ℝ) [Fact (0<S)] (e : ℝ ≃o ℝ) (hRef : AuxiliaryReferenceData S e)
    (a : ℝ) (ha : 0<a) (σ₀ α₀ : ℝ) (hσ₀ : 0≤σ₀)
    (ρ : ℝ → ℝ) (hρ : ∀ t : ℝ,0≤t → ρ t=(a^4+30*t)^(1/4:ℝ)) (p₀ : ℂ)
    (P : ℝ) (χ₀ : ℝ ≃o ℝ) (hχ : ContDiff ℝ ∞ (χ₀ : ℝ → ℝ))
    (hχinv : ContDiff ℝ ∞ (χ₀.symm : ℝ → ℝ))
    (hdeck : ∀ x,χ₀ (x+S/Real.sqrt 2)=χ₀ x+P)
    (Y : ℝ → ℝ → ℂ)
    (hY : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => Y z.1 z.2)
      (Ici (0:ℝ) ×ˢ (univ : Set ℝ)))
    (hYper : ∀ t : ℝ,0≤t → Function.Periodic (Y t) P)
    (hreg : ∀ t : ℝ,0<t → ∀ s,deriv (Y t) s≠0)
    (hFlow : ∀ t : ℝ,0<t → ∀ s,
      (conj (deriv (fun z => Y z s) t)*(I*deriv (Y t) s/(‖deriv (Y t) s‖:ℂ))).re=
        -planarElasticForce (Y t) s)
    (h₀ : ℝ → ℝ) (hh₀ : ContDiff ℝ ∞ h₀) (hp₀ : Function.Periodic h₀ S)
    (x₀ : CircleSobolevSpace S 2) (hx₀ : ‖x₀‖<flowNeighborhoodHeightRadius S)
    (hvalue : ∀ x : ℝ,circleSobolevH1Embedding S (circleSobolevInclusion S 1 x₀)
      (x:AddCircle S)=(h₀ x:ℂ))
    (hbase : ∀ x,Y (physicalTime a σ₀) (χ₀ (x/Real.sqrt 2))=p₀+
      (ρ (physicalTime a σ₀):ℂ)*(Complex.exp ((α₀:ℂ)*I)*
        (bernoulliCurve (e.symm x)+(h₀ x:ℂ)*(I*bernoulliAuxiliaryTangent e x))))
    (ψ : CircleL2 S) (G : C(AddCircle S,ℂ))
    (hG : ∀ x : ℝ,G (x:AddCircle S)=
      (((conj (bernoulliAuxiliaryTangent e x)*bernoulliAuxiliaryCurve e x).re+
        ((conj (bernoulliAuxiliaryTangent e x)*bernoulliAuxiliaryCurve e x).im+Real.sqrt 2*h₀ x)*
          deriv (fun s => Real.sqrt 2*h₀ s) x/
            (1-bernoulliAuxiliaryCurvature e x*(Real.sqrt 2*h₀ x)):ℝ):ℂ))
    (hGpair : (inner ℂ ψ (circleContinuousL2 S G)).re≠0) :
    Nonempty (BernoulliLocalFlowNeighborhood S e a σ₀ α₀ ρ p₀ χ₀ Y h₀ ψ) := by
  obtain ⟨hβ,hβper,hT,hTper,hκ,hκper,hframe⟩ := hRef
  obtain ⟨Γ,V,hΓ,hV,hd,hΓper,hVper,hcoupling⟩ :=
    normalized_flow_family S a ha σ₀ α₀ hσ₀ ρ hρ p₀ P χ₀ hχ hdeck Y hY hYper
  have hρpos (t : ℝ) (ht : 0≤t) : 0<ρ t := by
    rw [hρ t ht]
    exact Real.rpow_pos_of_pos (add_pos_of_pos_of_nonneg (pow_pos ha 4)
      (mul_nonneg (by norm_num) ht)) _
  have ht₀ : 0≤physicalTime a σ₀ := ((physical_time_inverse a ha).2.1 σ₀).2.2.1 hσ₀
  have hρne : (ρ (physicalTime a σ₀):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (hρpos _ ht₀).ne'
  have hInitial (x : ℝ) : Γ ((0,0),x)=bernoulliAuxiliaryCurve e x+
      I*((Real.sqrt 2*h₀ x:ℝ):ℂ)*bernoulliAuxiliaryTangent e x := by
    have hc := hcoupling (0,0) (by simp) x
    simp only [add_zero] at hc
    rw [hbase] at hc
    exact hc.trans (undo_base_rotation (Real.sqrt 2) α₀ (ρ (physicalTime a σ₀):ℂ) p₀
      (bernoulliCurve (e.symm x)) (bernoulliAuxiliaryTangent e x) (h₀ x) hρne)
  obtain ⟨r,hr,hclose⟩ := flow_neighborhood_box S (bernoulliAuxiliaryCurve e)
    (bernoulliAuxiliaryTangent e) (bernoulliAuxiliaryCurvature e) h₀
    (fun x => (hframe x).1) (fun x => (hframe x).2.1)
    (fun x => (hframe x).2.2.1) (fun x => (hframe x).2.2.2)
    hh₀ x₀ hvalue hx₀ Γ V hΓ.continuousOn hV.continuousOn hd hΓper hVper hInitial
  let B := insert ((0:ℝ),0) (Ioo 0 r ×ˢ Ioo (-r) r)
  have hBC : B⊆Ici (0:ℝ) ×ˢ (univ : Set ℝ) := by
    intro q hq
    rcases hq with rfl|hq
    · simp
    · exact ⟨hq.1.1.le,mem_univ _⟩
  have hYat (t : ℝ) (ht : 0<t) (s : ℝ) :
      ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => Y z.1 z.2) (t,s) :=
    hY.contDiffAt (prod_mem_nhds (Ici_mem_nhds ht) univ_mem)
  refine ⟨{
    timeRadius := r, angleRadius := r, timePositive := hr, anglePositive := hr,
    gamma := Γ, velocity := V, delta := 1/100, curvatureBound := 3, speedBound := 1+1/100,
    gammaSmooth := hΓ.mono (fun z hz => ⟨hBC hz.1,hz.2⟩),
    referenceSmooth := hβ, tangentSmooth := hT, curvatureSmooth := hκ,
    initialSmooth := hh₀, initialPeriodic := hp₀, gammaDerivative := fun q hq => hd q (hBC hq),
    referenceDerivative := fun x => (hframe x).1,
    tangentDerivative := fun x => (hframe x).2.1,
    tangentUnit := fun x => (hframe x).2.2.1,
    speed := fun q hq x => (hclose q hq x).2.2,
    gammaPeriodic := fun q hq => hΓper q (hBC hq), referencePeriodic := hβper,
    tangentPeriodic := hTper, curvaturePeriodic := hκper, initial := hInitial,
    deltaPositive := by norm_num, curvatureNonnegative := by norm_num,
    projectionSmall := by norm_num, graphRegular := by norm_num,
    positionClose := fun q hq x => (hclose q hq x).1,
    tangentClose := fun q hq x => (hclose q hq x).2.1,
    curvatureBounded := fun x => (hframe x).2.2.2,
    coupling := fun q hq => hcoupling q (hBC hq), initialRotation := G,
    initialRotationValue := hG, initialPair := hGpair,
    originalParameterSmooth := hχ, originalParameterInverseSmooth := hχinv,
    scale := fun t ht => ⟨hρpos t ht,hρ t ht,
      physical_normalization_derivatives_of_formula a ha ρ hρ t⟩,
    flowSpace := fun t ht => contDiff_iff_contDiffAt.mpr
      (fun s => (hYat t ht s).comp s (contDiffAt_const.prodMk contDiffAt_id)),
    flowRegular := hreg,
    flowDifferentiable := fun t ht s => (hYat t ht s).differentiableAt (by simp),
    flowEquation := hFlow }⟩

variable (T S : ℝ) [Fact (0<T)] [Fact (0<S)]

set_option maxHeartbeats 1000000 in
/-- The actual profile supplies one H2 threshold for a local normalized
neighborhood of every smooth given free elastic flow at a common orbit
point. The threshold is independent of time, scale, center, angle and the
given flow; the time and angle box is obtained from its actual continuity.
No smallness of any higher height norm is assumed. -/
theorem bernoulli_cover_local_flow_neighborhood
    (e : ℝ ≃o ℝ)
    (he : ∀ u,e u=∫ t in (0:ℝ)..u,Real.sqrt 2*‖bernoulliVelocity t‖)
    (hT : T=e (2*Real.pi)) (q p : C(AddCircle T,ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (hE : ∀ x,2*(p x)^2+(q x)^4=1)
    (hqlift : ∀ x : ℝ,q (x:AddCircle T)=(bernoulliProfileQ (e.symm x):ℂ))
    (hplift : ∀ x : ℝ,p (x:AddCircle T)=(bernoulliProfileP (e.symm x):ℂ))
    (hqreal : ∀ x,conj (q x)=q x) (hpreal : ∀ x,conj (p x)=p x)
    (hs : ∀ n : ℤ,fourierCoeff (q^2:C(AddCircle T,ℂ)) (-n)=
      fourierCoeff (q^2:C(AddCircle T,ℂ)) n)
    (hc : ∀ j : ℕ,fourierCoeff (q^2:C(AddCircle T,ℂ)) (2*(j:ℤ))=
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ,fourierCoeff (q^2:C(AddCircle T,ℂ)) (2*n+1)=0)
    (hr : (2*Real.pi/T)^2=lemniscateFrequencySquared)
    (ψ : circleH4Domain T)
    (hnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p)=1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ=0)
    (M : ℕ) (hM : 0<M) (hS : S=(M:ℝ)*T) :
    let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
    ∃ η>0,∀ a : ℝ,0<a → ∀ σ₀ : ℝ,0≤σ₀ → ∀ α₀ : ℝ,
      ∀ ρ : ℝ → ℝ,(∀ t : ℝ,0≤t → ρ t=(a^4+30*t)^(1/4:ℝ)) →
      ∀ p₀ : ℂ,∀ P : ℝ,∀ χ₀ : ℝ ≃o ℝ,
      ContDiff ℝ ∞ (χ₀ : ℝ → ℝ) → ContDiff ℝ ∞ (χ₀.symm : ℝ → ℝ) →
      (∀ x,χ₀ (x+S/Real.sqrt 2)=χ₀ x+P) →
      ∀ Y : ℝ → ℝ → ℂ,
      ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => Y z.1 z.2) (Ici (0:ℝ) ×ˢ (univ : Set ℝ)) →
      (∀ t : ℝ,0≤t → Function.Periodic (Y t) P) →
      (∀ t : ℝ,0<t → ∀ s,deriv (Y t) s≠0) →
      (∀ t : ℝ,0<t → ∀ s,
        (conj (deriv (fun z => Y z s) t)*(I*deriv (Y t) s/(‖deriv (Y t) s‖:ℂ))).re=
          -planarElasticForce (Y t) s) →
      ∀ h₀ : ℝ → ℝ,∀ hh₀ : ContDiff ℝ ∞ h₀,∀ hp₀ : Function.Periodic h₀ S,
      ∀ x₀ : CircleSobolevSpace S 2,‖x₀‖<η →
      circleSobolevCoordinate S 2 0 x₀=circleContinuousL2 S
        (periodicCircleFunction S (fun x : ℝ => (h₀ x:ℂ))
          (fun x => congrArg Complex.ofReal (hp₀ x))
          (Complex.continuous_ofReal.comp hh₀.continuous)) →
      (∀ x,Y (physicalTime a σ₀) (χ₀ (x/Real.sqrt 2))=p₀+
        (ρ (physicalTime a σ₀):ℂ)*(Complex.exp ((α₀:ℂ)*I)*
          (bernoulliCurve (e.symm x)+(h₀ x:ℂ)*(I*bernoulliAuxiliaryTangent e x)))) →
      Nonempty (BernoulliLocalFlowNeighborhood S e a σ₀ α₀ ρ p₀ χ₀ Y h₀ (Ψ:CircleL2 S)) := by
  dsimp only
  let Q := circlePeriodicExtension T S M hS q
  let P := circlePeriodicExtension T S M hS p
  let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
  have hdata := (paper_periodic_cover_modulated_tame_data T S q p hq hp hE hqreal hpreal
    hs hc ho hr ψ hnorm hψzero M hM hS).2.2
  have hRef := auxiliary_reference_data T S e he hT q p hq hqlift M hS (Ψ:CircleL2 S) hdata.2.1
  refine flow_neighborhood_radius
    (bernoulli_cover_local_profile_neighborhood T S q p hq hp hE hqreal hpreal hs hc ho hr
      ψ hnorm hψzero M hM hS) ?_
  intro η hη hProfile
  have hC1 : 0<flowNeighborhoodHeightRadius S := by
    dsimp only [flowNeighborhoodHeightRadius]
    positivity
  refine ⟨min η (flowNeighborhoodHeightRadius S),lt_min hη hC1,?_⟩
  intro a ha σ₀ hσ₀ α₀ ρ hρ p₀ P₀ χ₀ hχ hχinv hdeck Y hY hYper hreg hFlow
    h₀ hh₀ hp₀ x₀ hx₀ hvalue hbase
  let f₀ : C(AddCircle S,ℂ) := periodicCircleFunction S (fun x : ℝ => (h₀ x:ℂ))
    (fun x => congrArg Complex.ofReal (hp₀ x)) (Complex.continuous_ofReal.comp hh₀.continuous)
  have hval : circleSobolevH1Embedding S (circleSobolevInclusion S 1 x₀)=f₀ := by
    apply ContinuousMap.toLp_injective (p:=2) (𝕜:=ℂ) AddCircle.haarAddCircle
    change circleContinuousL2 S _=circleContinuousL2 S _
    rw [circle_sobolev_h1_embedding_l2]
    exact hvalue
  have hpoint (x : ℝ) : circleSobolevH1Embedding S (circleSobolevInclusion S 1 x₀)
      (x:AddCircle S)=(h₀ x:ℂ) := by rw [hval]; rfl
  have hQ (x : ℝ) : Q (x:AddCircle S)=(bernoulliProfileQ (e.symm x):ℂ) := hqlift x
  have hP (x : ℝ) : P (x:AddCircle S)=(bernoulliProfileP (e.symm x):ℂ) := hplift x
  refine flow_neighborhood_witness (auxiliary_initial_rotation S e he Q P hQ hP (Ψ:CircleL2 S)
    hdata.1 η hProfile.1 hProfile.2.1 h₀ hh₀ hp₀ x₀
      (hx₀.trans_le (min_le_left _ _)) hpoint) ?_
  intro G hG
  exact actual_flow_neighborhood S e hRef a ha σ₀ α₀ hσ₀ ρ hρ p₀ P₀ χ₀ hχ hχinv hdeck
    Y hY hYper hreg hFlow h₀ hh₀ hp₀ x₀ (hx₀.trans_le (min_le_right _ _)) hpoint hbase
    (Ψ:CircleL2 S) G hG.1 hG.2

end Lemniscate
