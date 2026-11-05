import Lemniscate.BernoulliClassicalModulationConverse
import Lemniscate.NormalGraphContinuousFlow
import Lemniscate.NormalGraphAngularVelocity
import Lemniscate.PeriodicParabolicClassicalTime
import Lemniscate.PeriodicParabolicEstimates

/-! The actual modulated Bernoulli equation at positive times.
The velocity is constructed in C(circle) from the H5 representative and
the actual angular velocity. Its equality with the recorded MR velocity
is proved almost everywhere before applying the classical-time theorem.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped Topology ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

private theorem continuous_representative_data
    {A B : Prop} {P Q R : ℝ → Prop} {Z : Prop}
    (h : A ∧ B ∧ ∃ δ > 0, P δ ∧ Q δ ∧ R δ)
    (k : A → B → ∀ δ, 0 < δ → P δ → Q δ → R δ → Z) : Z := by
  obtain ⟨ha,hb,δ,hδ,hP,hQ,hR⟩ := h
  exact k ha hb δ hδ hP hQ hR

private theorem positive_radius_data
    {P : ℝ → Prop} {Z : Prop} (h : ∃ δ > 0, P δ)
    (k : ∀ δ, 0 < δ → P δ → Z) : Z := by
  obtain ⟨δ,hδ,hP⟩ := h
  exact k δ hδ hP

private def continuousHeightValue :
    CircleSobolevSpace T 2 →L[ℂ] C(AddCircle T,ℂ) :=
  (circleSobolevH1Embedding T).comp (circleSobolevInclusion T 1)

private theorem classical_five_data
    (f : CircleSobolevSpace T 5) (g : CircleSobolevSpace T 2)
    (hfg : circleSobolevInclusion T 2
      (circleSobolevInclusion T 3 (circleSobolevInclusion T 4 f))=g)
    (hg : circleSobolevConjugation T 2 g=g) :
    let H := circleSobolevClassicalJet T 4 f
    (∀ j x, ((H j x).re:ℂ)=H j x) ∧
      (∀ j : Fin 4, HasCircleDeriv T (H j.castSucc) (H j.succ)) ∧
      (∀ j : Fin 4, circleSobolevContinuousJet T (circleSobolevInclusion T 4 f) j=H j.castSucc) ∧
      circleSobolevCoordinate T 4 4 (circleSobolevInclusion T 4 f)=circleContinuousL2 T (H 4) ∧
      continuousHeightValue T g=H 0 := by
  let H := circleSobolevClassicalJet T 4 f
  have hval : circleSobolevCoordinate T 5 0 f=circleSobolevCoordinate T 2 0 g :=
    congrArg (circleSobolevCoordinate T 2 0) hfg
  have hgr : circleConjugate T (circleSobolevCoordinate T 2 0 g)=
      circleSobolevCoordinate T 2 0 g := by
    simpa only [circle_sobolev_conjugation_coordinate] using
      congrArg (circleSobolevCoordinate T 2 0) hg
  have hfr : circleSobolevConjugation T 5 f=f := by
    apply circle_sobolev_value_injective T 5
    exact (circle_sobolev_conjugation_coordinate T 5 0 f).trans
      ((congrArg (circleConjugate T) hval).trans (hgr.trans hval.symm))
  refine ⟨?_,circle_sobolev_classical_jet_deriv T 4 f,?_,
    (circle_sobolev_classical_jet_l2 T 4 f 4).symm,?_⟩
  · intro j x
    have hs : star (H j)=H j :=
      (circle_sobolev_classical_jet_conjugation T 4 f j).symm.trans
        (congrArg (fun u : CircleSobolevSpace T 5 => circleSobolevClassicalJet T 4 u j) hfr)
    apply Complex.conj_eq_iff_re.mp
    exact congrArg (fun z : C(AddCircle T,ℂ) => z x) hs
  · intro j
    apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
    change circleContinuousL2 T
      (circleSobolevContinuousJet T (circleSobolevInclusion T 4 f) j)=
        circleContinuousL2 T (circleSobolevClassicalJet T 4 f j.castSucc)
    rw [(circle_sobolev_classical_jet_l2 T 3),circle_sobolev_classical_jet_l2]
    rfl
  · apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
    change circleContinuousL2 T
      (circleSobolevH1Embedding T (circleSobolevInclusion T 1 g))=
        circleContinuousL2 T (circleSobolevClassicalJet T 4 f 0)
    rw [circle_sobolev_h1_embedding_l2,circle_sobolev_classical_jet_l2]
    exact hval.symm

private theorem height_product_small_radius (K : BackgroundJetOver C(AddCircle T,ℂ)) :
    ∃ δ > 0, ∀ g : CircleSobolevSpace T 2, ‖g‖ < δ → ∀ x : AddCircle T,
      ‖K.k x*continuousHeightValue T g x‖ < (1/2:ℝ) := by
  have hc : ContinuousAt (fun g : CircleSobolevSpace T 2 =>
      ‖K.k*continuousHeightValue T g‖) 0 :=
    (continuous_const.mul (continuousHeightValue T).continuous).norm.continuousAt
  have hz : ‖K.k*continuousHeightValue T (0 : CircleSobolevSpace T 2)‖ < (1/2:ℝ) := by
    simp only [map_zero,mul_zero,norm_zero]
    norm_num
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hc.eventually_lt continuousAt_const hz)
  refine ⟨δ,hδ,fun g hg x => ?_⟩
  exact ((K.k*continuousHeightValue T g).norm_coe_le_norm x).trans_lt
    (hball (by simpa only [Metric.mem_ball,dist_zero_right] using hg))

private theorem modulated_flow_reconstruction
    (K : BackgroundJetOver C(AddCircle T,ℂ)) (c : ℝ) (ψ : CircleL2 T)
    (f : CircleSobolevSpace T 4) :
    circleNormalGraphModulatedFlow T K c ψ f=circleNormalGraphFlow T K c f-
      circleNormalGraphAngularVelocity T K c ψ f • circleNormalGraphRotationField T K
        (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)) := by
  simp only [circleNormalGraphModulatedFlow,circleNormalGraphNormalizedRotation,
    circleNormalGraphAngularVelocity,div_eq_mul_inv,smul_smul]

set_option maxHeartbeats 1600000 in
/-- The actual MR solution has the classical real modulated height equation
on every closed time interval carrying its continuous H5 representative,
including the initial right time derivative when the interval starts at zero.
The reference curve, normal and curvature are the actual Bernoulli frame. -/
theorem bernoulli_parabolic_classical_equation
    (e : ℝ ≃o ℝ) (he : ∀ u, e u=∫ t in (0:ℝ)..u, Real.sqrt 2*‖bernoulliVelocity t‖)
    (q p : C(AddCircle T,ℂ))
    (hq : ∀ x : ℝ, q (x:AddCircle T)=(bernoulliProfileQ (e.symm x):ℂ))
    (hp : ∀ x : ℝ, p (x:AddCircle T)=(bernoulliProfileP (e.symm x):ℂ)) (ψ : CircleL2 T) :
    ∃ δ > 0, ∀ τ : ℝ, 0 < τ → ∀ U : CircleParabolicSpace T τ,
      ‖circleParabolicCurve T τ U‖ < δ →
      ∀ r₀ : ℝ, ∀ hr₀ : 0 ≤ r₀, ∀ hr₀1 : r₀ < 1,
      ∀ W : C(Icc r₀ (1:ℝ),CircleSobolevSpace T 5),
      (∀ r : Icc r₀ (1:ℝ), circleSobolevInclusion T 2
        (circleSobolevInclusion T 3 (circleSobolevInclusion T 4 (W r)))=
          circleParabolicCurve T τ U ⟨(r:ℝ),hr₀.trans r.property.1,r.property.2⟩) →
      (∀ r : unitInterval, circleSobolevConjugation T 2 (circleParabolicCurve T τ U r)=
        circleParabolicCurve T τ U r) →
      ∀ ω : C(Icc r₀ (1:ℝ),ℝ),
      (∀ r : Icc r₀ (1:ℝ), (ω r:ℂ)=circleNormalGraphAngularVelocity T
        (circleBernoulliBackground T q p) (15/2) ψ (circleSobolevInclusion T 4 (W r))) →
      (∀ᵐ r ∂volume, circleParabolicTimeDerivative T τ U r=
        circleNormalGraphModulatedFlow T (circleBernoulliBackground T q p) (15/2) ψ
          (circleParabolicH4 T τ U r)) →
      let φ := fun s : ℝ => e.symm (Real.sqrt 2*s)
      let β := bernoulliCurve ∘ φ
      let t := fun s : ℝ => bernoulliVelocity (φ s)/(‖bernoulliVelocity (φ s)‖:ℂ)
      let n := fun s : ℝ => I*t s
      let k := fun s : ℝ => 3*bernoulliProfileQ (φ s)
      let h : ℝ → ℝ → ℝ := fun r s => (circleSobolevH1Embedding T
        (circleSobolevInclusion T 1
          (circleParabolicCurve T τ U (Set.projIcc (0:ℝ) 1 zero_le_one r)))
          ((Real.sqrt 2*s):AddCircle T)).re
      let h₁ : ℝ → ℝ → ℝ := fun r s => Real.sqrt 2*
        (circleSobolevClassicalJet T 4 (W (Set.projIcc r₀ 1 hr₀1.le r)) 1
          ((Real.sqrt 2*s):AddCircle T)).re
      ∀ r : ℝ, r₀ ≤ r → r ≤ 1 → ∀ s : ℝ,
        HasDerivAt (h r) (h₁ r s) s ∧ 0 < 1-k s*h r s ∧
        HasDerivWithinAt (fun z : ℝ => h z s)
          (τ*(normalGraphFlowRHS β n k (h r) (15/2) s-
            ω (Set.projIcc r₀ 1 hr₀1.le r)*
              ((conj (t s)*β s).re+((conj (t s)*β s).im+h r s)*h₁ r s/(1-k s*h r s)))) (Icc r₀ 1) r := by
  let K := circleBernoulliBackground T q p
  refine continuous_representative_data
    (circle_normal_graph_continuous_representatives T K (15/2)) ?_
  intro hRaw hRot δf hδf hDomain hRcont hGcont
  refine positive_radius_data (height_product_small_radius T K) ?_
  intro δr hδr hProduct
  let δ := min δf δr
  refine ⟨δ,lt_min hδf hδr,?_⟩
  intro τ hτ U hU r₀ hr₀ hr₀1 W hW hreal ω hω hPDE
  dsimp only
  let unitTime : Icc r₀ (1:ℝ) → unitInterval := fun r =>
    ⟨(r:ℝ),hr₀.trans r.property.1,r.property.2⟩
  let g : Icc r₀ (1:ℝ) → CircleSobolevSpace T 2 := fun r => circleParabolicCurve T τ U (unitTime r)
  let f : Icc r₀ (1:ℝ) → CircleSobolevSpace T 4 := fun r => circleSobolevInclusion T 4 (W r)
  let H : Icc r₀ (1:ℝ) → Fin 5 → C(AddCircle T,ℂ) := fun r => circleSobolevClassicalJet T 4 (W r)
  have hg (r : Icc r₀ (1:ℝ)) : ‖g r‖ < δ :=
    ((circleParabolicCurve T τ U).norm_coe_le_norm (unitTime r)).trans_lt hU
  have hfg (r : Icc r₀ (1:ℝ)) :
      circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (f r))=g r := hW r
  have hdata (r : Icc r₀ (1:ℝ)) := classical_five_data T (W r) (g r) (hW r) (hreal (unitTime r))
  have hDom (r : Icc r₀ (1:ℝ)) : f r ∈ circleNormalGraphDomain T K :=
    hDomain (W r) ((congrArg (fun z : CircleSobolevSpace T 2 => ‖z‖) (hW r)).trans_lt
      ((hg r).trans_le (min_le_left δf δr)))
  have hgc : Continuous g := (circleParabolicCurve T τ U).continuous.comp
    (continuous_subtype_val.subtype_mk _)
  have hRc : Continuous (fun r => circleNormalGraphContinuousFlow T K (15/2) (W r)) := by
    simpa only [Function.comp_def] using hRcont.comp_continuous W.continuous (fun r =>
      (congrArg (fun z : CircleSobolevSpace T 2 => ‖z‖) (hW r)).trans_lt
        ((hg r).trans_le (min_le_left δf δr)))
  have hGc : Continuous (fun r => circleNormalGraphContinuousRotation T K (g r)) := by
    apply hGcont.comp_continuous hgc
    intro r
    simpa only [Metric.mem_ball,dist_zero_right] using (hg r).trans_le (min_le_left δf δr)
  let V : C(Icc r₀ (1:ℝ),C(AddCircle T,ℂ)) :=
    ⟨fun r => circleNormalGraphContinuousFlow T K (15/2) (W r)-
      (ω r:ℂ) • circleNormalGraphContinuousRotation T K (g r),
      hRc.sub ((Complex.continuous_ofReal.comp ω.continuous).smul hGc)⟩
  have hVL2 (r : Icc r₀ (1:ℝ)) : circleContinuousL2 T (V r)=
      circleNormalGraphModulatedFlow T K (15/2) ψ (f r) := by
    have hF := hRaw (W r) (hDom r)
    have hG := hRot (g r)
    change (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ)
      (circleNormalGraphContinuousFlow T K (15/2) (W r)-
        (ω r:ℂ) • circleNormalGraphContinuousRotation T K (g r)) = _
    rw [map_sub,map_smul]
    exact (congrArg₂ (fun (a b : CircleL2 T) => a-b) hF
      (congrArg₂ (fun (a : ℂ) (b : CircleL2 T) => a • b) (hω r) hG)).trans
        ((congrArg (fun z : CircleSobolevSpace T 2 =>
            circleNormalGraphFlow T K (15/2) (f r)-
              circleNormalGraphAngularVelocity T K (15/2) ψ (f r) •
                circleNormalGraphRotationField T K z) (hfg r).symm).trans
          (modulated_flow_reconstruction T K (15/2) ψ (f r)).symm)
  have hVAE : ∀ᵐ (r : unitInterval) ∂volume, r₀ ≤ (r:ℝ) →
      circleParabolicTimeDerivative T τ U r=
        circleContinuousL2 T (V (Set.projIcc r₀ 1 hr₀1.le (r:ℝ))) := by
    filter_upwards [hPDE,circle_parabolic_h2_h4_ae T τ U] with r hpde hmr hr
    let z : Icc r₀ (1:ℝ) := ⟨(r:ℝ),hr,r.property.2⟩
    have hz : Set.projIcc r₀ 1 hr₀1.le (r:ℝ)=z := Set.projIcc_of_mem _ z.property
    have hu : unitTime z=r := Subtype.ext rfl
    have heq : f z=circleParabolicH4 T τ U r := by
      apply circle_sobolev_value_injective T 4
      change circleSobolevCoordinate T 2 0
        (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (f z))) =
          circleSobolevCoordinate T 2 0
            (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (circleParabolicH4 T τ U r)))
      exact congrArg (circleSobolevCoordinate T 2 0)
        ((hfg z).trans ((congrArg (circleParabolicCurve T τ U) hu).trans hmr))
    exact hpde.trans ((congrArg (circleNormalGraphModulatedFlow T K (15/2) ψ) heq.symm).trans
      ((hVL2 z).symm.trans (congrArg (fun z => circleContinuousL2 T (V z)) hz.symm)))
  let φ := fun s : ℝ => e.symm (Real.sqrt 2*s)
  let β := bernoulliCurve ∘ φ
  let t := fun s : ℝ => bernoulliVelocity (φ s)/(‖bernoulliVelocity (φ s)‖:ℂ)
  let n := fun s : ℝ => I*t s
  let k := fun s : ℝ => 3*bernoulliProfileQ (φ s)
  let h : ℝ → ℝ → ℝ := fun r s => (continuousHeightValue T
    (circleParabolicCurve T τ U (Set.projIcc (0:ℝ) 1 zero_le_one r))
      ((Real.sqrt 2*s):AddCircle T)).re
  let h₁ : ℝ → ℝ → ℝ := fun r s => Real.sqrt 2*
    (H (Set.projIcc r₀ 1 hr₀1.le r) 1 ((Real.sqrt 2*s):AddCircle T)).re
  have hreg (r : Icc r₀ (1:ℝ)) (x : ℝ) :
      0 < 1-3*bernoulliProfileQ (e.symm x)*(H r 0 (x:AddCircle T)).re := by
    have hb := hProduct (g r) ((hg r).trans_le (min_le_right δf δr)) (x:AddCircle T)
    have hc : (K.k (x:AddCircle T)*continuousHeightValue T (g r) (x:AddCircle T)).re=
        3*bernoulliProfileQ (e.symm x)*(H r 0 (x:AddCircle T)).re := by
      rw [(hdata r).2.2.2.2]
      simp only [K,circleBernoulliBackground,ContinuousMap.smul_apply,smul_eq_mul,hq x,
        Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
        Complex.re_ofNat,Complex.im_ofNat,zero_mul,mul_zero,sub_zero,add_zero]
      rfl
    have hle := Complex.re_le_norm
      (K.k (x:AddCircle T)*continuousHeightValue T (g r) (x:AddCircle T))
    rw [hc] at hle
    linarith
  intro r hr hr1 s
  let z : Icc r₀ (1:ℝ) := ⟨r,hr,hr1⟩
  have hz : Set.projIcc r₀ 1 hr₀1.le r=z := Set.projIcc_of_mem _ z.property
  have hunit : Set.projIcc (0:ℝ) 1 zero_le_one r=unitTime z :=
    Set.projIcc_of_mem _ ⟨hr₀.trans hr,hr1⟩
  have hheight : h r=fun s : ℝ => (H z 0 ((Real.sqrt 2*s):AddCircle T)).re := by
    apply congrArg (fun v : C(AddCircle T,ℂ) =>
      fun s : ℝ => (v ((Real.sqrt 2*s):AddCircle T)).re)
    exact (congrArg (fun a : unitInterval =>
      continuousHeightValue T (circleParabolicCurve T τ U a)) hunit).trans
        (hdata z).2.2.2.2
  have hs : HasDerivAt (h r) (h₁ r s) s := by
    have hd : HasDerivAt (fun x : ℝ => (H z 0 (x:AddCircle T)).re)
        (H z 1 ((Real.sqrt 2*s):AddCircle T)).re (Real.sqrt 2*s) := by
      simpa only [Function.comp_def,Complex.reCLM_apply] using!
        Complex.reCLM.hasFDerivAt.comp_hasDerivAt (Real.sqrt 2*s)
          ((hdata z).2.1 0 (Real.sqrt 2*s))
    have ha : HasDerivAt (fun x : ℝ => Real.sqrt 2*x) (Real.sqrt 2) s := by
      simpa only [id_eq,mul_one] using (hasDerivAt_id s).const_mul (Real.sqrt 2)
    rw [hheight]
    apply (hd.comp s ha).congr_deriv
    dsimp only [h₁]
    rw [hz]
    ring
  have hA : 0 < 1-k s*h r s := by
    simpa only [hheight,k,φ] using hreg z (Real.sqrt 2*s)
  have hpoint := (bernoulli_classical_graph_equation T e he q p hq hp
    (H z) (hdata z).1 (hdata z).2.1 (f z) (hdata z).2.2.1
      (hdata z).2.2.2.1 (hDom z) (hreg z)).2
  have hRpoint : circleNormalGraphContinuousFlow T K (15/2) (W z)
      ((Real.sqrt 2*s):AddCircle T)=((normalGraphFlowRHS β n k (h r) (15/2) s:ℝ):ℂ) := by
    have hp := hpoint (Real.sqrt 2*s)
    have hroot : Real.sqrt (2:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    have hscale : (Real.sqrt 2*s)/Real.sqrt 2=s := by field_simp [hroot]
    change circleNormalGraphContinuousFlow T K (15/2) (W z)
      ((Real.sqrt 2*s):AddCircle T)=
        ((normalGraphFlowRHS β n k
          (fun u : ℝ => (H z 0 ((Real.sqrt 2*u):AddCircle T)).re)
          (15/2) ((Real.sqrt 2*s)/Real.sqrt 2):ℝ):ℂ) at hp
    rw [hscale,← hheight] at hp
    exact hp
  have hGpoint : circleNormalGraphContinuousRotation T K (g z)
      ((Real.sqrt 2*s):AddCircle T)=
        (((conj (t s)*β s).re+((conj (t s)*β s).im+h r s)*h₁ r s/(1-k s*h r s):ℝ):ℂ) := by
    have hp := (bernoulli_classical_rotation_representation T e he q p hq hp
      (g z) (H z) (hdata z).1 (f z) (hfg z) (hdata z).2.2.1 (hDom z)).2 s
    simpa only [hheight,h₁,hz] using! hp
  have hVpoint : (V z ((Real.sqrt 2*s):AddCircle T)).re=
      normalGraphFlowRHS β n k (h r) (15/2) s-
        ω z*((conj (t s)*β s).re+((conj (t s)*β s).im+h r s)*h₁ r s/(1-k s*h r s)) := by
    change (circleNormalGraphContinuousFlow T K (15/2) (W z) ((Real.sqrt 2*s):AddCircle T)-
      (ω z:ℂ)*circleNormalGraphContinuousRotation T K (g z) ((Real.sqrt 2*s):AddCircle T)).re = _
    rw [hRpoint,hGpoint]
    simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero]
  have hBanach := circle_parabolic_hasDerivWithinAt_of_continuous_velocity T τ U r₀ hr₀ hr₀1 V hVAE
    r hr hr1
  have ht := (ContinuousMap.evalCLM ℝ ((Real.sqrt 2*s):AddCircle T)).hasFDerivAt.comp_hasDerivWithinAt r hBanach
  have htr := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt r ht
  have hVvalue : (V (Set.projIcc r₀ 1 hr₀1.le r) ((Real.sqrt 2*s):AddCircle T)).re=
      normalGraphFlowRHS β n k (h r) (15/2) s-
        ω (Set.projIcc r₀ 1 hr₀1.le r)*
          ((conj (t s)*β s).re+((conj (t s)*β s).im+h r s)*h₁ r s/(1-k s*h r s)) :=
    (congrArg (fun a : Icc r₀ (1:ℝ) => (V a ((Real.sqrt 2*s):AddCircle T)).re) hz).trans
      (hVpoint.trans (congrArg (fun a : ℝ =>
        normalGraphFlowRHS β n k (h r) (15/2) s-
          a*((conj (t s)*β s).re+((conj (t s)*β s).im+h r s)*h₁ r s/(1-k s*h r s)))
        (congrArg (fun a : Icc r₀ (1:ℝ) => ω a) hz.symm)))
  have hVscale : (τ • V (Set.projIcc r₀ 1 hr₀1.le r)
      ((Real.sqrt 2*s):AddCircle T)).re=
        τ*(V (Set.projIcc r₀ 1 hr₀1.le r) ((Real.sqrt 2*s):AddCircle T)).re := by
    simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero]
  refine ⟨hs,hA,?_⟩
  exact htr.congr_deriv (hVscale.trans (congrArg (fun a : ℝ => τ*a) hVvalue))

end Lemniscate
