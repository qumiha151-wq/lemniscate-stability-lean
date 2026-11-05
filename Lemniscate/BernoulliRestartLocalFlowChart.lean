import Lemniscate.BernoulliLocalFlowNeighborhood
import Lemniscate.BernoulliLocalFlowChart
import Lemniscate.BernoulliPhysicalGraphStability
import Lemniscate.PeriodicSobolevSmoothness
import Lemniscate.PeriodicParabolicInteriorTime
import Lemniscate.FreeElasticFlow

/-! One profile-dependent H2 radius gives the actual parabolic chart at
every common orbit point of the constructed evolution and a given flow. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Set Filter CoarseArithmetic
open scoped ContDiff Topology NNReal ENNReal ComplexConjugate

private theorem restart_radius_transport {P : ℝ → Prop} {Q : Prop}
    (h : ∃ r>0,P r) (k : ∀ r,0<r → P r → Q) : Q := by
  obtain ⟨r,hr,hP⟩ := h
  exact k r hr hP

private theorem denormalize_restart_point (y p r z : ℂ) (hr : r≠0)
    (h : (y-p)/r=z) : y=p+r*z := by
  have hh : y-p=z*r := (div_eq_iff hr).mp h
  calc
    y=(y-p)+p := by ring
    _=p+r*z := by rw [hh]; ring

set_option maxHeartbeats 800000 in
private theorem evolution_height_at_time
    (S : ℝ) [Fact (0<S)] (q p : C(AddCircle S,ℂ)) (ψ : CircleL2 S)
    (τ : ℝ) (hτ : 0<τ) (η : ℝ) (z₀ : CircleSobolevSpace S 2)
    (D : BernoulliNormalGraphEvolution S q p ψ τ hτ η z₀)
    (hInitial : ContDiff ℝ ∞ (fun x : ℝ => circleSobolevH1Embedding S
      (circleSobolevInclusion S 1 z₀) (x:AddCircle S))) (σ₀ : ℝ≥0) :
    let f := circleSobolevH1Embedding S (circleSobolevInclusion S 1 (D.u σ₀))
    let h := fun x : ℝ => (f (x:AddCircle S)).re
    ContDiff ℝ ∞ h ∧ Function.Periodic h S ∧
      (∀ x : ℝ,(h x:ℂ)=f (x:AddCircle S)) ∧ ‖D.u σ₀‖<η := by
  dsimp only
  let f := circleSobolevH1Embedding S (circleSobolevInclusion S 1 (D.u σ₀))
  have hConj : star f=f := by
    apply ContinuousMap.toLp_injective (p:=2) (𝕜:=ℂ) AddCircle.haarAddCircle
    change circleContinuousL2 S (star f)=circleContinuousL2 S f
    rw [circle_continuous_l2_star,circle_sobolev_h1_embedding_l2]
    have hr := congrArg (circleSobolevCoordinate S 2 0) (D.real σ₀)
    simp only [circle_sobolev_conjugation_coordinate] at hr
    simpa only [circle_sobolev_inclusion_coordinate,Fin.castSucc_zero] using hr
  have hsmooth : ContDiff ℝ ∞ (fun x : ℝ => f (x:AddCircle S)) := by
    by_cases hz : σ₀=0
    · subst σ₀
      simpa only [f,D.initial] using! hInitial
    · have hpos : (0:ℝ)<(σ₀:ℝ) := by
        exact_mod_cast (pos_iff_ne_zero.mpr hz : (0:ℝ≥0)<σ₀)
      let t : Ioi (0:ℝ) := ⟨(σ₀:ℝ),hpos⟩
      have hNN : (⟨(t:ℝ),t.property.le⟩ : ℝ≥0)=σ₀ := Subtype.ext rfl
      apply circle_smooth_of_all_sobolev_lifts S f
      intro n
      refine ⟨D.w (n+1) t,?_⟩
      simpa only [f,circle_sobolev_h1_embedding_l2,circle_sobolev_inclusion_coordinate,
        Fin.castSucc_zero,hNN] using D.positiveValue (n+1) t
  refine ⟨Complex.reCLM.contDiff.comp hsmooth,?_,?_,?_⟩
  · intro x
    exact congrArg (fun z : AddCircle S => (f z).re) (AddCircle.coe_add_period S x)
  · intro x
    exact Complex.conj_eq_iff_re.mp (congrArg (fun F : C(AddCircle S,ℂ) => F (x:AddCircle S)) hConj)
  · have hbound (m : ℕ) (r : unitInterval) : ‖circleParabolicCurve S τ (D.U m) r‖<η :=
      ((circleParabolicCurve S τ (D.U m)).norm_coe_le_norm r).trans_lt
        ((norm_fst_le (D.U m).val).trans_lt (D.segmentSmall m))
    by_cases hz : σ₀=0
    · subst σ₀
      have ht : circleParabolicSegmentTime τ hτ 0 (0:unitInterval)=0 := by
        apply Subtype.ext
        simp [circleParabolicSegmentTime]
      have hr : D.u 0=circleParabolicCurve S τ (D.U 0) 0 :=
        (congrArg D.u ht).symm.trans (D.segments 0 0)
      exact (congrArg (fun f : CircleSobolevSpace S 2 => ‖f‖) hr).trans_lt
        (hbound 0 0)
    · have hpos : (0:ℝ)<(σ₀:ℝ) := by
        exact_mod_cast (pos_iff_ne_zero.mpr hz : (0:ℝ≥0)<σ₀)
      obtain ⟨m,r,_,_,ht⟩ := circle_parabolic_interior_time τ hτ (σ₀:ℝ) hpos σ₀ le_rfl
      have hr : D.u σ₀=circleParabolicCurve S τ (D.U m) r :=
        (congrArg D.u ht).symm.trans (D.segments m r)
      exact (congrArg (fun f : CircleSobolevSpace S 2 => ‖f‖) hr).trans_lt
        (hbound m r)

private abbrev RestartChartConclusion
    (S : ℝ) [Fact (0<S)] (e : ℝ ≃o ℝ) (q p : C(AddCircle S,ℂ)) (ψ : CircleL2 S)
    (η : ℝ) : Prop :=
  (∀ f : CircleSobolevSpace S 4,
    ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)‖<η →
      f∈circleNormalGraphDomain S (circleBernoulliBackground S q p)) ∧
  (∀ g : CircleSobolevSpace S 2,‖g‖<η → circleNormalGraphRotationFunctional S ψ
    (circleNormalGraphRotationField S (circleBernoulliBackground S q p) g)≠0) ∧
  ContinuousOn (circleNormalGraphModulatedFlow S (circleBernoulliBackground S q p) (15/2) ψ)
    {f : CircleSobolevSpace S 4 | ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)‖<η} ∧
  (∀ d : ℝ,0<d → ∀ U V : CircleParabolicSpace S d,
    circleParabolicInitialValue S d U=circleParabolicInitialValue S d V →
    ‖circleParabolicCurve S d U‖<η → ‖circleParabolicCurve S d V‖<η →
    (∀ᵐ r : unitInterval ∂volume,circleParabolicTimeDerivative S d U r=
      circleNormalGraphModulatedFlow S (circleBernoulliBackground S q p) (15/2) ψ
        (circleParabolicH4 S d U r)) →
    (∀ᵐ r : unitInterval ∂volume,circleParabolicTimeDerivative S d V r=
      circleNormalGraphModulatedFlow S (circleBernoulliBackground S q p) (15/2) ψ
        (circleParabolicH4 S d V r)) → U=V) ∧
  ∀ τ : ℝ,∀ hτ : 0<τ,∀ z₀ : CircleSobolevSpace S 2,
    ∀ D : BernoulliNormalGraphEvolution S q p ψ τ hτ η z₀,
    ∀ h₀ : ℝ → ℝ,∀ hh₀ : ContDiff ℝ ∞ h₀,∀ hp₀ : Function.Periodic h₀ S,
    circleSobolevCoordinate S 2 0 z₀=circleContinuousL2 S
      (periodicCircleFunction S (fun x : ℝ => (h₀ x:ℂ))
        (fun x => congrArg Complex.ofReal (hp₀ x))
        (Complex.continuous_ofReal.comp hh₀.continuous)) →
    ∀ a : ℝ,0<a → ∀ α : ℝ,∀ ρ : ℝ → ℝ,
    (∀ t : ℝ,0≤t → 0<ρ t ∧ ρ t=(a^4+30*t)^(1/4:ℝ)) →
    ∀ p₀ : ℂ,∀ P : ℝ,∀ Y : ℝ → ℝ → ℂ,
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => Y z.1 z.2) (Ici (0:ℝ) ×ˢ (univ : Set ℝ)) →
    (∀ t : ℝ,0≤t → Function.Periodic (Y t) P) → IsFreeElasticFlow Y →
    ∀ σ₀ : ℝ≥0,∀ χ₀ : ℝ ≃o ℝ,
    ContDiff ℝ ∞ (χ₀ : ℝ → ℝ) → ContDiff ℝ ∞ (χ₀.symm : ℝ → ℝ) →
    (∀ s,χ₀ (s+S/Real.sqrt 2)=χ₀ s+P) →
    (∀ s,(Y (physicalTime a (σ₀:ℝ)) (χ₀ s)-p₀)/(ρ (physicalTime a (σ₀:ℝ)):ℂ)=
      Complex.exp (((α+D.theta (σ₀:ℝ)):ℂ)*I)*
        (bernoulliCurve (e.symm (Real.sqrt 2*s))+
          ((circleSobolevH1Embedding S (circleSobolevInclusion S 1 (D.u σ₀))
            ((Real.sqrt 2*s):AddCircle S)).re:ℂ)*(I*bernoulliAuxiliaryTangent e (Real.sqrt 2*s)))) →
    Nonempty (BernoulliLocalFlowChart S e q p ψ η (D.u σ₀)
      a (σ₀:ℝ) (α+D.theta (σ₀:ℝ)) ρ p₀ χ₀ Y)

variable (T S : ℝ) [Fact (0<T)] [Fact (0<S)]

set_option maxHeartbeats 1200000 in
/-- One radius, chosen from the actual profile before any evolution or
given flow, supplies the analytic profile conditions and the actual local
chart at every common orbit point. The same evolution and radius are used
throughout; only its continuous H2 norm is required to be small. -/
theorem bernoulli_restart_local_flow_chart
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
    let Q := circlePeriodicExtension T S M hS q
    let P := circlePeriodicExtension T S M hS p
    let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
    ∃ η>0,RestartChartConclusion S e Q P (Ψ:CircleL2 S) η := by
  dsimp only
  let Q := circlePeriodicExtension T S M hS q
  let P := circlePeriodicExtension T S M hS p
  let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
  let K := circleBernoulliBackground S Q P
  have hdata := (paper_periodic_cover_modulated_tame_data T S q p hq hp hE hqreal hpreal
    hs hc ho hr ψ hnorm hψzero M hM hS).2.2
  have hQ (x : ℝ) : Q (x:AddCircle S)=(bernoulliProfileQ (e.symm x):ℂ) := hqlift x
  have hP (x : ℝ) : P (x:AddCircle S)=(bernoulliProfileP (e.symm x):ℂ) := hplift x
  refine restart_radius_transport
    (bernoulli_cover_local_profile_neighborhood T S q p hq hp hE hqreal hpreal hs hc ho hr
      ψ hnorm hψzero M hM hS) ?_
  intro ηP hηP hProfile
  refine restart_radius_transport
    (bernoulli_cover_local_flow_neighborhood T S e he hT q p hq hp hE hqlift hplift
      hqreal hpreal hs hc ho hr ψ hnorm hψzero M hM hS) ?_
  intro ηC hηC hCoarse
  let η := min ηP ηC
  have hη : 0<η := lt_min hηP hηC
  have hηP' : η≤ηP := min_le_left _ _
  have hηC' : η≤ηC := min_le_right _ _
  have hDomain (f : CircleSobolevSpace S 4)
      (hf : ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)‖<η) :
      f∈circleNormalGraphDomain S K := hProfile.1 f (hf.trans_le hηP')
  have hDen (g : CircleSobolevSpace S 2) (hg : ‖g‖<η) :
      circleNormalGraphRotationFunctional S (Ψ:CircleL2 S)
        (circleNormalGraphRotationField S K g)≠0 := hProfile.2.1 g (hg.trans_le hηP')
  have hMod : ContinuousOn (circleNormalGraphModulatedFlow S K (15/2) (Ψ:CircleL2 S))
      {f : CircleSobolevSpace S 4 | ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)‖<η} :=
    hProfile.2.2.1.mono (fun f hf => hf.trans_le hηP')
  refine ⟨η,hη,hDomain,hDen,hMod,?_,?_⟩
  · intro d hd U V hinit hU hV hPU hPV
    exact hProfile.2.2.2 d hd U V hinit (hU.trans_le hηP') (hV.trans_le hηP') hPU hPV
  intro τ hτ z₀ D h₀ hh₀ hp₀ hvalue a ha α ρ hρ p₀ P₀ Y hY hYper hFlow
    σ₀ χ₀ hχ hχinv hdeck hbase
  let F₀ : C(AddCircle S,ℂ) := periodicCircleFunction S (fun x : ℝ => (h₀ x:ℂ))
    (fun x => congrArg Complex.ofReal (hp₀ x)) (Complex.continuous_ofReal.comp hh₀.continuous)
  have hInitialValue : circleSobolevH1Embedding S (circleSobolevInclusion S 1 z₀)=F₀ := by
    apply ContinuousMap.toLp_injective (p:=2) (𝕜:=ℂ) AddCircle.haarAddCircle
    change circleContinuousL2 S _=circleContinuousL2 S _
    rw [circle_sobolev_h1_embedding_l2]
    exact hvalue
  have hInitial : ContDiff ℝ ∞ (fun x : ℝ => circleSobolevH1Embedding S
      (circleSobolevInclusion S 1 z₀) (x:AddCircle S)) := by
    have heq : (fun x : ℝ => circleSobolevH1Embedding S
        (circleSobolevInclusion S 1 z₀) (x:AddCircle S))=(fun x : ℝ => (h₀ x:ℂ)) := by
      funext x
      rw [hInitialValue]
      rfl
    rw [heq]
    exact Complex.ofRealCLM.contDiff.comp hh₀
  let f := circleSobolevH1Embedding S (circleSobolevInclusion S 1 (D.u σ₀))
  let h := fun x : ℝ => (f (x:AddCircle S)).re
  obtain ⟨hSmooth,hPeriodic,hReal,hSmall⟩ := evolution_height_at_time S Q P (Ψ:CircleL2 S)
    τ hτ η z₀ D hInitial σ₀
  let F : C(AddCircle S,ℂ) := periodicCircleFunction S (fun x : ℝ => (h x:ℂ))
    (fun x => congrArg Complex.ofReal (hPeriodic x))
    (Complex.continuous_ofReal.comp hSmooth.continuous)
  have hF : F=f := by
    ext x
    refine QuotientAddGroup.induction_on x ?_
    intro x
    exact hReal x
  have hValue : circleSobolevCoordinate S 2 0 (D.u σ₀)=circleContinuousL2 S F := by
    rw [hF]
    simp only [f,circle_sobolev_h1_embedding_l2,circle_sobolev_inclusion_coordinate,Fin.castSucc_zero]
  have ht : 0≤physicalTime a (σ₀:ℝ) := ((physical_time_inverse a ha).2.1 (σ₀:ℝ)).2.2.1 σ₀.property
  have hρne : (ρ (physicalTime a (σ₀:ℝ)):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (hρ _ ht).1.ne'
  have hsqrt : Real.sqrt (2:ℝ)≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hscale (x : ℝ) : Real.sqrt 2*(x/Real.sqrt 2)=x := by field_simp [hsqrt]
  have hBasePhysical (x : ℝ) : Y (physicalTime a (σ₀:ℝ)) (χ₀ (x/Real.sqrt 2))=p₀+
      (ρ (physicalTime a (σ₀:ℝ)):ℂ)*(Complex.exp (((α+D.theta (σ₀:ℝ)):ℂ)*I)*
        (bernoulliCurve (e.symm x)+(h x:ℂ)*(I*bernoulliAuxiliaryTangent e x))) := by
    have heq := hbase (x/Real.sqrt 2)
    rw [hscale] at heq
    exact denormalize_restart_point _ _ _ _ hρne heq
  let N := Classical.choice (hCoarse a ha (σ₀:ℝ) σ₀.property (α+D.theta (σ₀:ℝ))
    ρ (fun t ht => (hρ t ht).2) p₀ P₀ χ₀ hχ hχinv hdeck Y hY hYper
    (fun t ht s => (Classical.choose_spec (hFlow t ht.le s)).2.1)
    (free_elastic_flow_normal_equation Y hFlow) h hSmooth hPeriodic (D.u σ₀)
    (hSmall.trans_le hηC') hValue (fun x => by
      simpa only [Complex.ofReal_add] using! hBasePhysical x))
  exact bernoulli_local_flow_chart S e he Q P hQ hP (Ψ:CircleL2 S) hdata.1
    a (σ₀:ℝ) (α+D.theta (σ₀:ℝ)) ha σ₀.property ρ p₀ χ₀ Y h N (D.u σ₀)
    hValue (D.phase σ₀) η hη hSmall hDomain hDen hMod

end Lemniscate
