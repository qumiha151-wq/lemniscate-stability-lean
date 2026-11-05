import Lemniscate.BernoulliParabolicSmoothStability
import Lemniscate.BernoulliParabolicEndpointSmoothing
import Lemniscate.BernoulliPhysicalNormalGraphFlow
import Lemniscate.BernoulliReferenceNormalGraph
import Lemniscate.NormalGraphInitialAngularVelocity
import Lemniscate.NormalGraphGlobalConvergence
import Lemniscate.NormalGraphConvergenceEstimate
import Lemniscate.RotationAngleConvergence
import Lemniscate.RotationAngleInitialDerivative
import Lemniscate.PeriodicParabolicInteriorTime
import Lemniscate.PeriodicSmoothClassicalJet
import Lemniscate.BernoulliCircleProfile

/-! Global free elastic flow from a small smooth normal height.
The evolution, its angular velocity and its limiting rotation are obtained
from the actual modulated equation. Only the initial H2 norm is small. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set CoarseArithmetic
open scoped ContDiff ENNReal Topology NNReal ComplexConjugate

set_option maxHeartbeats 800000 in
/-- One actual real normal-height evolution, together with its initial
closed-time lift and the angle of its moving normal graph. -/
structure BernoulliNormalGraphEvolution
    (T : ℝ) [Fact (0<T)] (q p : C(AddCircle T,ℂ)) (ψ : CircleL2 T)
    (τ : ℝ) (hτ : 0<τ) (η : ℝ) (x₀ : CircleSobolevSpace T 2) where
  u : C(ℝ≥0,CircleSobolevSpace T 2)
  U : ℕ → CircleParabolicSpace T τ
  w : ∀ n : ℕ, C(Ioi (0:ℝ),CircleSobolevSpace T n)
  initialLift : C(unitInterval,CircleSobolevSpace T 5)
  omega : ℝ → ℝ
  initialOmega : C(unitInterval,ℝ)
  theta : ℝ → ℝ
  thetaLimit : ℝ
  initial : u 0=x₀
  segmentSmall : ∀ m, ‖U m‖<η
  segments : ∀ m r, u (circleParabolicSegmentTime τ hτ m r)=circleParabolicCurve T τ (U m) r
  equation : ∀ m, ∀ᵐ r ∂volume, circleParabolicTimeDerivative T τ (U m) r=
    circleNormalGraphModulatedFlow T (circleBernoulliBackground T q p) (15/2) ψ
      (circleParabolicH4 T τ (U m) r)
  real : ∀ t, circleSobolevConjugation T 2 (u t)=u t
  phase : ∀ t, inner ℂ ψ (circleSobolevCoordinate T 2 0 (u t))=0
  positiveValue : ∀ n (t : Ioi (0:ℝ)), circleSobolevCoordinate T n 0 (w n t)=
    circleSobolevCoordinate T 2 0 (u ⟨(t:ℝ),t.property.le⟩)
  positiveLimit : ∀ n, Tendsto (w n) atTop (𝓝 0)
  initialValue : ∀ r, circleSobolevInclusion T 2
    (circleSobolevInclusion T 3 (circleSobolevInclusion T 4 (initialLift r)))=
      circleParabolicCurve T τ (U 0) r
  omegaContinuous : ContinuousOn omega (Ioi (0:ℝ))
  omegaValue : ∀ t : Ioi (0:ℝ), (omega t:ℂ)=circleNormalGraphAngularVelocity T
    (circleBernoulliBackground T q p) (15/2) ψ (circleSobolevInclusion T 4 (w 5 t))
  initialOmegaValue : ∀ r, (initialOmega r:ℂ)=circleNormalGraphAngularVelocity T
    (circleBernoulliBackground T q p) (15/2) ψ
      (circleSobolevInclusion T 4 (initialLift r))
  omegaZero : omega 0=initialOmega 0
  thetaZero : theta 0=0
  thetaContinuous : Continuous theta
  thetaDerivative : ∀ t : ℝ, 0≤t → HasDerivWithinAt theta (omega t) (Ici (0:ℝ)) t
  thetaConvergence : Tendsto theta atTop (𝓝 thetaLimit)
  thetaTail : ∀ t₀ ν B : ℝ, 0<t₀ → 0<ν → 0≤B →
    (∀ t : ℝ,t₀≤t → |omega t|≤B*Real.exp (-ν*t)) →
    ∀ t : ℝ,t₀≤t → |thetaLimit-theta t|≤(B/ν)*Real.exp (-ν*t)

private theorem graph_curve_norm (T : ℝ) [Fact (0<T)]
    (τ : ℝ) (U : CircleParabolicSpace T τ) :
    ‖circleParabolicCurve T τ U‖≤‖U‖ := norm_fst_le U.val

private theorem graph_h4_norm (T : ℝ) [Fact (0<T)]
    (τ : ℝ) (U : CircleParabolicSpace T τ) :
    ‖circleParabolicH4 T τ U‖≤‖U‖ :=
  (norm_fst_le U.val.2).trans (norm_snd_le U.val)

private theorem graph_initial_norm (T : ℝ) [Fact (0<T)]
    (τ : ℝ) (U : CircleParabolicSpace T τ) :
    ‖circleParabolicInitialValue T τ U‖≤‖U‖ :=
  ((circleParabolicCurve T τ U).norm_coe_le_norm 0).trans (graph_curve_norm T τ U)

private theorem graph_rate_norm (r A μ t X : ℝ) (hr : 0≤r) (hA : 0≤A) (hX : 0≤X)
    (h : r^2≤A*Real.exp (-2*μ*t)*X^2) :
    r≤Real.sqrt A*X*Real.exp (-μ*t) := by
  have he : Real.exp (-2*μ*t)=Real.exp (-μ*t)^2 := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hs : r^2≤(Real.sqrt A*X*Real.exp (-μ*t))^2 := h.trans_eq (by
    rw [mul_pow,mul_pow,Real.sq_sqrt hA,he]
    ring)
  exact (sq_le_sq₀ hr (by positivity)).mp hs

private theorem graph_interior_cover (τ : ℝ) (hτ : 0<τ)
    (t : ℝ≥0) (ht : 0<t) :
    ∃ (m : ℕ) (r : unitInterval),
      0<(r:ℝ) ∧ (r:ℝ)<1 ∧ circleParabolicSegmentTime τ hτ m r=t := by
  obtain ⟨m,r,hr,hlo,heq⟩ := circle_parabolic_interior_time τ hτ t ht t le_rfl
  have hmin : (0:ℝ)<min (1/2:ℝ) ((t:ℝ)/τ) :=
    lt_min (by norm_num) (div_pos ht hτ)
  exact ⟨m,r,hmin.trans_le hlo,hr,heq⟩

private theorem graph_value_lift (T : ℝ) [Fact (0<T)]
    (u : C(ℝ≥0,CircleSobolevSpace T 2))
    (w : ∀ n : ℕ, C(Ioi (0:ℝ),CircleSobolevSpace T n))
    (hw : ∀ n (t : Ioi (0:ℝ)), circleSobolevCoordinate T n 0 (w n t)=
      circleSobolevCoordinate T 2 0 (u ⟨(t:ℝ),t.property.le⟩))
    (t : Ioi (0:ℝ)) :
    circleSobolevInclusion T 2 (circleSobolevInclusion T 3
      (circleSobolevInclusion T 4 (w 5 t)))=u ⟨(t:ℝ),t.property.le⟩ := by
  apply circle_sobolev_value_injective T 2
  exact hw 5 t

private theorem graph_h1_real (T : ℝ) [Fact (0<T)]
    (u : CircleSobolevSpace T 2) (hu : circleSobolevConjugation T 2 u=u) :
    ∀ x, (((circleSobolevH1Embedding T (circleSobolevInclusion T 1 u)) x).re:ℂ)=
      circleSobolevH1Embedding T (circleSobolevInclusion T 1 u) x := by
  let f := circleSobolevH1Embedding T (circleSobolevInclusion T 1 u)
  have hstar : star f=f := by
    apply ContinuousMap.toLp_injective (p:=2) (𝕜:=ℂ) AddCircle.haarAddCircle
    change circleContinuousL2 T (star f)=circleContinuousL2 T f
    rw [circle_continuous_l2_star,circle_sobolev_h1_embedding_l2]
    change circleConjugate T (circleSobolevCoordinate T 2 0 u)=
      circleSobolevCoordinate T 2 0 u
    rw [← circle_sobolev_conjugation_coordinate,hu]
  intro x
  exact Complex.conj_eq_iff_re.mp (congrArg (fun f : C(AddCircle T,ℂ) => f x) hstar)

private theorem graph_height_jet (T : ℝ) [Fact (0<T)]
    (u : C(ℝ≥0,CircleSobolevSpace T 2))
    (w : ∀ n : ℕ, C(Ioi (0:ℝ),CircleSobolevSpace T n))
    (hw : ∀ n (t : Ioi (0:ℝ)), circleSobolevCoordinate T n 0 (w n t)=
      circleSobolevCoordinate T 2 0 (u ⟨(t:ℝ),t.property.le⟩))
    (j : ℕ) (t : Ioi (0:ℝ)) :
    circleSobolevClassicalJet T j (w (j+1) t) 0=
      circleSobolevH1Embedding T (circleSobolevInclusion T 1
        (u ⟨(t:ℝ),t.property.le⟩)) := by
  apply ContinuousMap.toLp_injective (p:=2) (𝕜:=ℂ) AddCircle.haarAddCircle
  change circleContinuousL2 T _=circleContinuousL2 T _
  rw [circle_sobolev_classical_jet_l2,circle_sobolev_h1_embedding_l2]
  exact hw (j+1) t

private theorem graph_classical_height (T : ℝ) [Fact (0<T)]
    (u : C(ℝ≥0,CircleSobolevSpace T 2))
    (w : ∀ n : ℕ, C(Ioi (0:ℝ),CircleSobolevSpace T n))
    (hw : ∀ n (t : Ioi (0:ℝ)), circleSobolevCoordinate T n 0 (w n t)=
      circleSobolevCoordinate T 2 0 (u ⟨(t:ℝ),t.property.le⟩))
    (t : Ioi (0:ℝ)) :
    ContDiff ℝ ∞ (fun x : ℝ => circleSobolevH1Embedding T
      (circleSobolevInclusion T 1 (u ⟨(t:ℝ),t.property.le⟩)) (x:AddCircle T)) := by
  apply contDiff_infty.mpr
  intro j
  have hc : ContDiff ℝ (j:ℕ∞ω)
      (fun x : ℝ => circleSobolevClassicalJet T j (w (j+1) t) 0 (x:AddCircle T)) :=
    (circle_sobolev_classical_regularity T j (w (j+1) t)).1
  simpa only [graph_height_jet T u w hw j t] using! hc

private abbrev GraphSmallSolutionProperty
    (T : ℝ) [Fact (0<T)] (q p : C(AddCircle T,ℂ)) (ψ : CircleL2 T)
    (τ : ℝ) (hτ : 0<τ) (g η : ℝ) : Prop :=
  (∃ ε>0, ∀ x₀ : CircleSobolevSpace T 2,
    circleSobolevConjugation T 2 x₀=x₀ →
    inner ℂ ψ (circleSobolevCoordinate T 2 0 x₀)=0 → ‖x₀‖≤ε →
    ∃ u : C(ℝ≥0,CircleSobolevSpace T 2), ∃ U : ℕ → CircleParabolicSpace T τ,
      u 0=x₀ ∧
      (∀ m, ‖U m‖<η ∧ circleParabolicConjugation T τ (U m)=U m ∧
        ∀ᵐ r ∂volume, circleParabolicTimeDerivative T τ (U m) r=
          circleNormalGraphModulatedFlow T (circleBernoulliBackground T q p) (15/2) ψ
            (circleParabolicH4 T τ (U m) r)) ∧
      (∀ m r, u (circleParabolicSegmentTime τ hτ m r)=circleParabolicCurve T τ (U m) r) ∧
      (∀ t, circleSobolevConjugation T 2 (u t)=u t ∧
        inner ℂ ψ (circleSobolevCoordinate T 2 0 (u t))=0) ∧
      ∃ w : ∀ n : ℕ, C(Ioi (0:ℝ),CircleSobolevSpace T n),
        (∀ n (t : Ioi (0:ℝ)), circleSobolevCoordinate T n 0 (w n t)=
          circleSobolevCoordinate T 2 0 (u ⟨(t:ℝ),t.property.le⟩)) ∧
        ∀ n, Tendsto (w n) atTop (𝓝 0)) ∧
  (∀ μ : ℝ, 0<μ → μ<g → ∀ n : ℕ, ∀ t₀>0,
    ∃ ε>0, ∃ C>0,
    ∀ (u : C(ℝ≥0,CircleSobolevSpace T 2)) (U : ℕ → CircleParabolicSpace T τ),
      (∀ m r, u (circleParabolicSegmentTime τ hτ m r)=circleParabolicCurve T τ (U m) r) →
      (∀ m, ‖U m‖<η) →
      (∀ m, ∀ᵐ r ∂volume, circleParabolicTimeDerivative T τ (U m) r=
        circleNormalGraphModulatedFlow T (circleBernoulliBackground T q p) (15/2) ψ
          (circleParabolicH4 T τ (U m) r)) →
      circleSobolevConjugation T 2 (u 0)=u 0 →
      inner ℂ ψ (circleSobolevCoordinate T 2 0 (u 0))=0 → ‖u 0‖≤ε →
      ∀ w : C(Ioi (0:ℝ),CircleSobolevSpace T n),
        (∀ t : Ioi (0:ℝ), circleSobolevCoordinate T n 0 (w t)=
          circleSobolevCoordinate T 2 0 (u ⟨(t:ℝ),t.property.le⟩)) →
        ∀ t : Ioi (0:ℝ), t₀≤(t:ℝ) →
          ‖w t‖^2≤C*Real.exp (-2*μ*(t:ℝ))*‖u 0‖^2)

private theorem graph_positive_transport {P : ℝ → Prop} {Q : Prop}
    (h : ∃ a>0,P a) (k : ∀ a,0<a → P a → Q) : Q := by
  obtain ⟨a,ha,hP⟩ := h
  exact k a ha hP

private theorem graph_two_positive_transport {P : ℝ → ℝ → Prop} {Q : Prop}
    (h : ∃ a>0,∃ b>0,P a b) (k : ∀ a,0<a → ∀ b,0<b → P a b → Q) : Q := by
  obtain ⟨a,ha,b,hb,hP⟩ := h
  exact k a ha b hb hP

private theorem graph_witness_transport {X : Type*} {P : X → Prop} {Q : Prop}
    (h : ∃ x,P x) (k : ∀ x,P x → Q) : Q := by
  obtain ⟨x,hx⟩ := h
  exact k x hx

private theorem graph_two_witness_transport {X Y : Type*} {P : X → Y → Prop} {Q : Prop}
    (h : ∃ x,∃ y,P x y) (k : ∀ x y,P x y → Q) : Q := by
  obtain ⟨x,y,hxy⟩ := h
  exact k x y hxy

set_option maxHeartbeats 1200000 in
private theorem graph_evolution_of_small_solutions
    (T : ℝ) [Fact (0<T)] (q p : C(AddCircle T,ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (hE : ∀ x,2*(p x)^2+(q x)^4=1)
    (ψ : CircleL2 T) (hψ : circleConjugate T ψ=ψ)
    (hpair : inner ℂ ψ (circleContinuousL2 T (circleBernoulliBackground T q p).b)≠0)
    (hK : (⟨star (circleBernoulliBackground T q p).k,
      star (circleBernoulliBackground T q p).ks,star (circleBernoulliBackground T q p).kss,
      star (circleBernoulliBackground T q p).ksss,star (circleBernoulliBackground T q p).eta,
      star (circleBernoulliBackground T q p).b⟩ : BackgroundJetOver C(AddCircle T,ℂ))=
        circleBernoulliBackground T q p)
    (hneutral : ∀ f : CircleSobolevSpace T 4, circleNormalGraphRotationFunctional T ψ
      (circleNormalGraphDerivative T (circleBernoulliBackground T q p) (15/2) f)=0)
    (τ : ℝ) (hτ : 0<τ)
    (e : CircleParabolicSpace T τ ≃L[ℂ] (CircleSobolevSpace T 2×CircleTimeL2 T))
    (he : e.toContinuousLinearMap=circleParabolicLowerOrderData T τ
      (circleSobolevCoordinate T 2 0+
        circleSobolevLowerOrderOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))))
    (g : ℝ) (hg : 0<g)
    (hsolve : ∀ ηreq>0,∃ η>0,η<ηreq ∧ GraphSmallSolutionProperty T q p ψ τ hτ g η)
    (ηreq : ℝ) (hηreq : 0<ηreq) :
    ∃ ε>0,∀ x₀ : CircleSobolevSpace T 2,
      circleSobolevConjugation T 2 x₀=x₀ →
      inner ℂ ψ (circleSobolevCoordinate T 2 0 x₀)=0 → ‖x₀‖≤ε →
      ∀ F : ℕ → C(AddCircle T,ℂ), (∀ j,HasCircleDeriv T (F j) (F (j+1))) →
      circleSobolevCoordinate T 2 0 x₀=circleContinuousL2 T (F 0) →
      Nonempty (BernoulliNormalGraphEvolution T q p ψ τ hτ ηreq x₀) := by
  let K := circleBernoulliBackground T q p
  have hFzero := (bernoulli_sobolev_flow_linearization T q p hE).1
  refine graph_two_positive_transport
    (circle_global_normal_graph_angular_velocity T K (15/2) ψ hpair hFzero hneutral hK hψ) ?_
  intro δΩ hδΩ CΩ hCΩ hGlobal
  refine graph_positive_transport
    (circle_initial_normal_graph_angular_velocity T K (15/2) ψ hpair hK hψ) ?_
  intro δI hδI hInitial
  refine graph_positive_transport
    (bernoulli_parabolic_endpoint_smoothing T q p hq hp hE τ hτ.ne' e he) ?_
  intro ηE hηE hEndpoint
  let η₀ := min ηreq (min δΩ (min δI (min ηE
    (min 1 (ηE/(2*(CΩ+1)))))))
  have hη₀ : 0<η₀ := by
    dsimp only [η₀]
    exact lt_min hηreq (lt_min hδΩ (lt_min hδI (lt_min hηE
      (lt_min zero_lt_one (div_pos hηE (by positivity))))))
  refine graph_positive_transport (hsolve η₀ hη₀) ?_
  intro η hη hdata
  obtain ⟨hηle,hqual,hquant⟩ := hdata
  have hηreq' : η<ηreq := hηle.trans_le (min_le_left _ _)
  have hηΩ : η<δΩ := hηle.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hηI : η<δI := hηle.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hηE' : η<ηE := hηle.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hη₁ : η<1 := hηle.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))))
  have hηbound : η<ηE/(2*(CΩ+1)) := hηle.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))))
  refine graph_positive_transport hqual ?_
  intro ε₀ hε₀ hqual
  refine graph_two_positive_transport
    (hquant (g/2) (half_pos hg) (by linarith) 2 1 zero_lt_one) ?_
  intro ε₂ hε₂ C₂ hC₂ hdecay₂
  refine graph_two_positive_transport
    (hquant (g/2) (half_pos hg) (by linarith) 4 1 zero_lt_one) ?_
  intro ε₄ hε₄ C₄ hC₄ hdecay₄
  refine ⟨min ε₀ (min ε₂ ε₄),lt_min hε₀ (lt_min hε₂ hε₄),?_⟩
  intro x₀ hreal hphase hsmall F hF hvalue
  refine graph_two_witness_transport (hqual x₀ hreal hphase (hsmall.trans (min_le_left _ _))) ?_
  intro u U hdata
  obtain ⟨hu₀,hU,hrep,hrealphase,w,hw,hwzero⟩ := hdata
  have hUsmall : ∀ m,‖U m‖<η := fun m => (hU m).1
  have hPDE := fun m => (hU m).2.2
  have hrealU := fun t => (hrealphase t).1
  have hphaseU := fun t => (hrealphase t).2
  have hw₂ (t : Ioi (0:ℝ)) : w 2 t=u ⟨(t:ℝ),t.property.le⟩ :=
    circle_sobolev_value_injective T 2 (hw 2 t)
  let w₄ : C(Ioi (0:ℝ),CircleSobolevSpace T 4) := w 4
  have hw₄ (t : Ioi (0:ℝ)) : circleSobolevInclusion T 2
      (circleSobolevInclusion T 3 (w₄ t))=u ⟨(t:ℝ),t.property.le⟩ := by
    apply circle_sobolev_value_injective T 2
    exact hw 4 t
  have heps₂ : ‖u 0‖≤ε₂ := by
    rw [hu₀]
    exact hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heps₄ : ‖u 0‖≤ε₄ := by
    rw [hu₀]
    exact hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hrate₂ := hdecay₂ u U hrep hUsmall hPDE (hu₀.symm ▸ hreal)
    (hu₀.symm ▸ hphase) heps₂ (w 2) (hw 2)
  have hrate₄ := hdecay₄ u U hrep hUsmall hPDE (hu₀.symm ▸ hreal)
    (hu₀.symm ▸ hphase) heps₄ (w 4) (hw 4)
  let A₂ := Real.sqrt C₂*‖u 0‖
  let A₄ := Real.sqrt C₄*‖u 0‖
  have hdecay (t : Ioi (0:ℝ)) (ht : (1:ℝ)≤t) :
      ‖u ⟨(t:ℝ),t.property.le⟩‖≤A₂*Real.exp (-(g/2)*(t:ℝ)) ∧
        ‖w₄ t‖≤A₄*Real.exp (-(g/2)*(t:ℝ)) := by
    constructor
    · rw [← hw₂ t]
      exact graph_rate_norm _ _ _ _ _ (norm_nonneg _) hC₂.le (norm_nonneg _) (hrate₂ t ht)
    · exact graph_rate_norm _ _ _ _ _ (norm_nonneg _) hC₄.le (norm_nonneg _) (hrate₄ t ht)
  let ω₁ : ℝ → ℝ := fun t => if ht : 0<t then
    (circleNormalGraphAngularVelocity T K (15/2) ψ (w₄ ⟨t,ht⟩)).re else 0
  have hωdata := hGlobal τ hτ u U w₄
    (fun m => (graph_curve_norm T τ (U m)).trans_lt ((hUsmall m).trans hηΩ))
    hrep (graph_interior_cover τ hτ) hw₄ hrealU hPDE 1 (g/2) A₂ A₄
    zero_lt_one (half_pos hg) (by dsimp only [A₂]; positivity)
    (by dsimp only [A₄]; positivity) hdecay
  change (∀ t:ℝ,t≤0 → ω₁ t=0) ∧ _ at hωdata
  obtain ⟨hωzero,hωvalue,hωcont,hsegments,hlocal,hωbound⟩ := hωdata
  refine graph_witness_transport (hsegments 0) ?_
  intro φ hφ
  obtain ⟨hφpoint,hφω,hφnorm,hφPDE⟩ := hφ
  have hηscalar : η+CΩ*η^2<ηE := by
    have hquad : η^2≤η := by nlinarith [hη₁.le]
    have hh := (lt_div_iff₀ (by positivity : 0<2*(CΩ+1))).mp hηbound
    calc
      η+CΩ*η^2≤η+CΩ*η := add_le_add le_rfl (mul_le_mul_of_nonneg_left hquad hCΩ.le)
      _<ηE := by nlinarith [mul_pos hCΩ hη]
  have hφsmall : ‖circleParabolicInitialValue T τ (U 0)‖+‖φ‖<ηE := by
    have hcurve := (graph_curve_norm T τ (U 0)).trans_lt (hUsmall 0)
    have hfourth := (graph_h4_norm T τ (U 0)).trans_lt (hUsmall 0)
    have hH4nonneg : (0:ℝ)≤‖circleParabolicH4 T τ (U 0)‖ := by
      change 0≤ENNReal.toReal _
      exact ENNReal.toReal_nonneg
    have hprod : ‖φ‖≤CΩ*η^2 := hφnorm.trans (by
      calc
        CΩ*‖circleParabolicCurve T τ (U 0)‖*‖circleParabolicH4 T τ (U 0)‖≤CΩ*η*η :=
          mul_le_mul (mul_le_mul_of_nonneg_left hcurve.le hCΩ.le) hfourth.le
            hH4nonneg (mul_nonneg hCΩ.le hη.le)
        _=CΩ*η^2 := by ring)
    exact (add_le_add ((graph_initial_norm T τ (U 0)).trans (hUsmall 0).le) hprod).trans_lt hηscalar
  have hInitialValue : circleParabolicInitialValue T τ (U 0)=x₀ := by
    calc
      circleParabolicInitialValue T τ (U 0)=u (circleParabolicSegmentTime τ hτ 0 0) :=
        (hrep 0 0).symm
      _=u 0 := by congr 1; apply Subtype.ext; simp [circleParabolicSegmentTime]
      _=x₀ := hu₀
  refine graph_witness_transport
    (hEndpoint (U 0) ((hUsmall 0).trans hηE') φ hφsmall hφPDE F hF
      (hInitialValue.symm ▸ hvalue) 5) ?_
  intro W₀ hW₀value
  have hW₀ (r : unitInterval) : circleSobolevInclusion T 2
      (circleSobolevInclusion T 3 (circleSobolevInclusion T 4 (W₀ r)))=
        circleParabolicCurve T τ (U 0) r := by
    apply circle_sobolev_value_injective T 2
    exact hW₀value r
  refine graph_witness_transport (hInitial τ (U 0)
    ((graph_curve_norm T τ (U 0)).trans_lt ((hUsmall 0).trans hηI)) W₀ hW₀
      (fun r => by rw [← hrep 0 r]; exact hrealU _)) ?_
  intro Ω₀ hΩ₀
  have hωinitial (t : ℝ) (ht : 0<t) (htτ : t≤τ) :
      ω₁ t=Ω₀ (projIcc (0:ℝ) 1 zero_le_one (t/τ)) := by
    let r : unitInterval := ⟨t/τ,div_nonneg ht.le hτ.le,(div_le_one hτ).mpr htτ⟩
    have hr : projIcc (0:ℝ) 1 zero_le_one (t/τ)=r :=
      Set.projIcc_of_mem zero_le_one r.property
    have htime : (circleParabolicSegmentTime τ hτ 0 r:ℝ)=t := by
      have hh : τ*(t/τ)=t := by field_simp [hτ.ne']
      simpa only [circleParabolicSegmentTime,NNReal.coe_mk,Nat.cast_zero,zero_div,zero_add,r]
        using! hh
    let z : Ioi (0:ℝ) := ⟨t,ht⟩
    have hNN : circleParabolicSegmentTime τ hτ 0 r=⟨(z:ℝ),z.property.le⟩ := Subtype.ext htime
    have heq : circleSobolevInclusion T 4 (W₀ r)=w₄ z := by
      apply circle_sobolev_value_injective T 4
      change circleSobolevCoordinate T 2 0
        (circleSobolevInclusion T 2 (circleSobolevInclusion T 3
          (circleSobolevInclusion T 4 (W₀ r))))=
        circleSobolevCoordinate T 2 0 (circleSobolevInclusion T 2
          (circleSobolevInclusion T 3 (w₄ z)))
      rw [hW₀,hw₄,← hrep 0 r,hNN]
    rw [hr]
    apply Complex.ofReal_injective
    exact (hωvalue z).trans ((congrArg (circleNormalGraphAngularVelocity T K (15/2) ψ)
      heq.symm).trans (hΩ₀ r).symm)
  refine graph_two_witness_transport
    (rotation_angle_convergence ω₁ hlocal hωcont 1 (2*(g/2)) (CΩ*A₂*A₄)
      zero_lt_one (by positivity) (by dsimp only [A₂,A₄]; positivity) hωbound) ?_
  intro θ θlim hθdata
  obtain ⟨hθintegral,hθcont,hθzero,hθderiv,hθlim,hθtail⟩ := hθdata
  let ω₀ : ℝ → ℝ := fun t => if t=0 then Ω₀ 0 else ω₁ t
  have hω₀positive (t : ℝ) (ht : 0<t) : ω₀ t=ω₁ t := if_neg ht.ne'
  have hω₀cont : ContinuousOn ω₀ (Ioi (0:ℝ)) :=
    hωcont.congr (fun t ht => hω₀positive t ht)
  have hθinitial : HasDerivWithinAt θ (Ω₀ 0) (Ici (0:ℝ)) 0 := by
    have hi := rotation_angle_initial_derivative τ hτ ω₁ Ω₀ hωinitial
    have heq : θ=(fun t => ∫ s in (0:ℝ)..t,ω₁ s) := funext hθintegral
    rw [heq]
    exact hi
  have hθwithin (t : ℝ) (ht : 0≤t) : HasDerivWithinAt θ (ω₀ t) (Ici (0:ℝ)) t := by
    by_cases hz : t=0
    · subst t
      simpa only [ω₀,if_pos rfl] using hθinitial
    · rw [hω₀positive t (lt_of_le_of_ne ht (Ne.symm hz))]
      exact (hθderiv t (lt_of_le_of_ne ht (Ne.symm hz))).hasDerivWithinAt
  have hωfull (t : Ioi (0:ℝ)) : (ω₀ t:ℂ)=circleNormalGraphAngularVelocity T K (15/2) ψ
      (circleSobolevInclusion T 4 (w 5 t)) := by
    have heq : w₄ t=circleSobolevInclusion T 4 (w 5 t) := by
      apply circle_sobolev_value_injective T 4
      exact (hw 4 t).trans (hw 5 t).symm
    rw [hω₀positive t t.property]
    exact (hωvalue t).trans (congrArg (circleNormalGraphAngularVelocity T K (15/2) ψ) heq)
  refine ⟨{
    u := u, U := U, w := w, initialLift := W₀, omega := ω₀, initialOmega := Ω₀,
    theta := θ, thetaLimit := θlim, initial := hu₀,
    segmentSmall := fun m => (hUsmall m).trans hηreq', segments := hrep,
    equation := hPDE, real := hrealU, phase := hphaseU, positiveValue := hw,
    positiveLimit := hwzero, initialValue := hW₀, omegaContinuous := hω₀cont,
    omegaValue := hωfull,
    initialOmegaValue := hΩ₀, omegaZero := by simp only [ω₀,if_pos rfl],
    thetaZero := hθzero, thetaContinuous := hθcont, thetaDerivative := hθwithin,
    thetaConvergence := hθlim,
    thetaTail := fun t₀ ν B ht₀ hν hB hb =>
      hθtail t₀ ν B ht₀ hν hB (fun t ht => by
        rw [← hω₀positive t (ht₀.trans_le ht)]
        exact hb t ht) }⟩

/-- The actual Bernoulli position and normal on every spectral cover are
smooth and periodic. This same reference geometry is used by both the
convergence estimate and the comparison of geometric curve families. -/
theorem bernoulli_reference_profile_geometry
    (T S : ℝ) [Fact (0<T)] [Fact (0<S)]
    (e : ℝ ≃o ℝ)
    (he : ∀ u,e u=∫ t in (0:ℝ)..u,Real.sqrt 2*‖bernoulliVelocity t‖)
    (hT : T=e (2*Real.pi))
    (q p : C(AddCircle T,ℂ)) (hq : HasCircleDeriv T q p)
    (hqlift : ∀ x : ℝ,q (x:AddCircle T)=(bernoulliProfileQ (e.symm x):ℂ))
    (M : ℕ) (hS : S=(M:ℝ)*T) (ψ : CircleL2 S)
    (hpair : inner ℂ ψ (circleContinuousL2 S
      (circleBernoulliBackground S
        (circlePeriodicExtension T S M hS q) (circlePeriodicExtension T S M hS p)).b)≠0) :
    let β := fun x : ℝ => bernoulliCurve (e.symm x)
    let ν := fun x : ℝ => I*(bernoulliVelocity (e.symm x)/
      (‖bernoulliVelocity (e.symm x)‖:ℂ))
    ContDiff ℝ ∞ β ∧ Function.Periodic β S ∧
      ContDiff ℝ ∞ ν ∧ Function.Periodic ν S := by
  subst T
  have hcurvature (x : ℝ) :
      (planarSignedCurvature bernoulliCurve (e.symm x):ℂ)=
        3*q (x:AddCircle (e (2*Real.pi))) := by
    rw [(bernoulli_arclength_profile_of_coordinate e he x).2.2.2,hqlift]
    simp only [Function.comp_apply,Complex.ofReal_mul,Complex.ofReal_ofNat]
  obtain ⟨_,hβ,hβper,hframe,_,_,_,_⟩ :=
    bernoulli_reference_normal_graph e he q p hq hcurvature M S hS ψ hpair
  dsimp only at hβ hβper hframe
  let B := fun x : ℝ => (Real.sqrt 2:ℂ)*bernoulliCurve (e.symm x)
  let t := fun x : ℝ => bernoulliVelocity (e.symm x)/(‖bernoulliVelocity (e.symm x)‖:ℂ)
  have ht : deriv B=t := funext fun x => (hframe x).1.deriv
  have htsmooth : ContDiff ℝ ∞ t := by
    rw [← ht]
    exact (contDiff_infty_iff_deriv.mp hβ).2
  have htper : Function.Periodic t S := by
    have hh := periodic_iterated_deriv S B hβper 1
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,ht] using hh
  have hsqrt : (Real.sqrt 2:ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  have hβeq : (fun x : ℝ => B x/(Real.sqrt 2:ℂ))=
      fun x : ℝ => bernoulliCurve (e.symm x) := by
    funext x
    dsimp only [B]
    field_simp [hsqrt]
  refine ⟨?_,?_,contDiff_const.mul htsmooth,?_⟩
  · exact hβeq ▸ hβ.div_const (Real.sqrt 2:ℂ)
  · intro x
    apply mul_left_cancel₀ hsqrt
    exact hβper x
  · intro x
    exact congrArg (I*·) (htper x)

private def graphNormalizedError
    (T : ℝ) [Fact (0<T)] (e : ℝ ≃o ℝ)
    (u : C(ℝ≥0,CircleSobolevSpace T 2)) (θ : ℝ → ℝ) (θlim α σ : ℝ) : ℝ → ℂ :=
  fun s : ℝ => Complex.exp (((α+θ σ):ℂ)*I)*
    (bernoulliCurve (e.symm (Real.sqrt 2*s))+
      circleSobolevH1Embedding T (circleSobolevInclusion T 1 (u (Real.toNNReal σ)))
        ((Real.sqrt 2*s):AddCircle T)*
          (I*(bernoulliVelocity (e.symm (Real.sqrt 2*s))/
            (‖bernoulliVelocity (e.symm (Real.sqrt 2*s))‖:ℂ))))-
    Complex.exp (((α+θlim):ℂ)*I)*bernoulliCurve (e.symm (Real.sqrt 2*s))

private theorem graph_rotation_exp (z : ℂ) :
    Complex.exp (I*z)=Complex.exp (z*I) := congrArg Complex.exp (mul_comm _ _)

set_option maxHeartbeats 1200000 in
private theorem graph_uniform_convergence_rate
    (T : ℝ) [Fact (0<T)] (e : ℝ ≃o ℝ)
    (q p : C(AddCircle T,ℂ)) (ψ : CircleL2 T)
    (τ : ℝ) (hτ : 0<τ) (g ηA ηB δΩ CΩ : ℝ)
    (hηA : ηB≤ηA) (hδΩ : ηB≤δΩ) (hCΩ : 0<CΩ)
    (hStable : GraphSmallSolutionProperty T q p ψ τ hτ g ηA)
    (hΩ : ∀ f : CircleSobolevSpace T 4,
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖<δΩ →
      ‖circleNormalGraphAngularVelocity T (circleBernoulliBackground T q p) (15/2) ψ f‖≤
        CΩ*‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖*‖f‖)
    (hβ : ContDiff ℝ ∞ (fun x : ℝ => bernoulliCurve (e.symm x)))
    (hβper : Function.Periodic (fun x : ℝ => bernoulliCurve (e.symm x)) T)
    (hν : ContDiff ℝ ∞ (fun x : ℝ => I*(bernoulliVelocity (e.symm x)/
      (‖bernoulliVelocity (e.symm x)‖:ℂ))))
    (hνper : Function.Periodic (fun x : ℝ => I*(bernoulliVelocity (e.symm x)/
      (‖bernoulliVelocity (e.symm x)‖:ℂ))) T)
    (t₀ μ : ℝ) (ht₀ : 0<t₀) (hμ : 0<μ) (hμg : μ<g) (j : ℕ) :
    ∃ ε>0,∃ C>0,∀ x₀ : CircleSobolevSpace T 2,
      ∀ D : BernoulliNormalGraphEvolution T q p ψ τ hτ ηB x₀,
      ‖x₀‖≤ε → ∀ α σ : ℝ,t₀≤σ →
        periodicCjNorm j (graphNormalizedError T e D.u D.theta D.thetaLimit α σ)≤
          C*Real.exp (-μ*σ)*‖x₀‖ := by
  refine graph_two_positive_transport (hStable.2 μ hμ hμg 2 t₀ ht₀) ?_
  intro ε₂ hε₂ C₂ hC₂ hDecay₂
  refine graph_two_positive_transport (hStable.2 μ hμ hμg 4 t₀ ht₀) ?_
  intro ε₄ hε₄ C₄ hC₄ hDecay₄
  refine graph_two_positive_transport (hStable.2 μ hμ hμg (j+1) t₀ ht₀) ?_
  intro εj hεj Cj hCj hDecayj
  let BΩ := CΩ*Real.sqrt C₂*Real.sqrt C₄
  let Bθ := BΩ/(2*μ)
  have hBΩ : 0≤BΩ := by dsimp only [BΩ]; positivity
  have hBθ : 0≤Bθ := div_nonneg hBΩ (by positivity)
  let B := fun x : ℝ => bernoulliCurve (e.symm x)
  let N := fun x : ℝ => I*(bernoulliVelocity (e.symm x)/(‖bernoulliVelocity (e.symm x)‖:ℂ))
  have horder : (j:ℕ∞ω)≤(∞:ℕ∞ω) := (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)).le
  refine graph_positive_transport
    (normal_graph_convergence_estimate T j B N (hβ.of_le horder) (hν.of_le horder)
      hβper hνper (Real.sqrt 2) (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
      Cj Bθ hCj hBθ) ?_
  intro C hC hEstimate
  refine ⟨min 1 (min ε₂ (min ε₄ εj)),
    lt_min zero_lt_one (lt_min hε₂ (lt_min hε₄ hεj)),C,hC,?_⟩
  intro x₀ D hsmall
  let X := ‖x₀‖
  have hX : X∈Icc (0:ℝ) 1 := ⟨norm_nonneg _,hsmall.trans (min_le_left _ _)⟩
  have hx₂ : ‖D.u 0‖≤ε₂ := by
    rw [D.initial]
    exact hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hx₄ : ‖D.u 0‖≤ε₄ := by
    rw [D.initial]
    exact hsmall.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hxj : ‖D.u 0‖≤εj := by
    rw [D.initial]
    exact hsmall.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hU : ∀ m,‖D.U m‖<ηA := fun m => (D.segmentSmall m).trans_le hηA
  have hrate₂ := hDecay₂ D.u D.U D.segments hU D.equation (D.real 0) (D.phase 0)
    hx₂ (D.w 2) (D.positiveValue 2)
  have hrate₄ := hDecay₄ D.u D.U D.segments hU D.equation (D.real 0) (D.phase 0)
    hx₄ (D.w 4) (D.positiveValue 4)
  have hratej := hDecayj D.u D.U D.segments hU D.equation (D.real 0) (D.phase 0)
    hxj (D.w (j+1)) (D.positiveValue (j+1))
  have hw₂ (t : Ioi (0:ℝ)) : D.w 2 t=D.u ⟨(t:ℝ),t.property.le⟩ :=
    circle_sobolev_value_injective T 2 (D.positiveValue 2 t)
  have hw₄ (t : Ioi (0:ℝ)) : circleSobolevInclusion T 2
      (circleSobolevInclusion T 3 (D.w 4 t))=D.u ⟨(t:ℝ),t.property.le⟩ := by
    apply circle_sobolev_value_injective T 2
    exact D.positiveValue 4 t
  have hsmallu (t : Ioi (0:ℝ)) : ‖D.u ⟨(t:ℝ),t.property.le⟩‖<ηB := by
    obtain ⟨m,r,_,_,heq⟩ := graph_interior_cover τ hτ ⟨(t:ℝ),t.property.le⟩ t.property
    have he := D.segments m r
    rw [heq] at he
    rw [he]
    exact ((circleParabolicCurve T τ (D.U m)).norm_coe_le_norm r).trans_lt
      ((graph_curve_norm T τ (D.U m)).trans_lt (D.segmentSmall m))
  have hωbound (s : ℝ) (hs : t₀≤s) :
      |D.omega s|≤(BΩ*X^2)*Real.exp (-(2*μ)*s) := by
    let t : Ioi (0:ℝ) := ⟨s,ht₀.trans_le hs⟩
    have heq : circleSobolevInclusion T 4 (D.w 5 t)=D.w 4 t := by
      apply circle_sobolev_value_injective T 4
      exact (D.positiveValue 5 t).trans (D.positiveValue 4 t).symm
    have hω : (D.omega s:ℂ)=circleNormalGraphAngularVelocity T
        (circleBernoulliBackground T q p) (15/2) ψ (D.w 4 t) :=
      (D.omegaValue t).trans (congrArg
        (circleNormalGraphAngularVelocity T (circleBernoulliBackground T q p) (15/2) ψ) heq)
    have hωre : D.omega s=(circleNormalGraphAngularVelocity T
        (circleBernoulliBackground T q p) (15/2) ψ (D.w 4 t)).re := by
      simpa only [Complex.ofReal_re] using congrArg Complex.re hω
    have hΩt := hΩ (D.w 4 t) (by rw [hw₄]; exact (hsmallu t).trans_le hδΩ)
    rw [hw₄] at hΩt
    have hn₂ : ‖D.u ⟨(t:ℝ),t.property.le⟩‖≤Real.sqrt C₂*X*Real.exp (-μ*s) := by
      have hh := hrate₂ t hs
      rw [hw₂,D.initial] at hh
      exact graph_rate_norm _ _ _ _ _ (norm_nonneg _) hC₂.le (norm_nonneg _) hh
    have hn₄ : ‖D.w 4 t‖≤Real.sqrt C₄*X*Real.exp (-μ*s) := by
      have hh := hrate₄ t hs
      rw [D.initial] at hh
      exact graph_rate_norm _ _ _ _ _ (norm_nonneg _) hC₄.le (norm_nonneg _) hh
    have hexp : Real.exp (-μ*s)*Real.exp (-μ*s)=Real.exp (-(2*μ)*s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      |D.omega s|≤‖circleNormalGraphAngularVelocity T
          (circleBernoulliBackground T q p) (15/2) ψ (D.w 4 t)‖ := by
        rw [hωre]
        exact Complex.abs_re_le_norm _
      _≤CΩ*‖D.u ⟨(t:ℝ),t.property.le⟩‖*‖D.w 4 t‖ := hΩt
      _≤CΩ*(Real.sqrt C₂*X*Real.exp (-μ*s))*(Real.sqrt C₄*X*Real.exp (-μ*s)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hn₂ hCΩ.le) hn₄ (norm_nonneg _) (by positivity)
      _=(CΩ*Real.sqrt C₂*Real.sqrt C₄*X^2)*(Real.exp (-μ*s)*Real.exp (-μ*s)) := by ring
      _=(BΩ*X^2)*Real.exp (-(2*μ)*s) := by rw [hexp]
  have htail := D.thetaTail t₀ (2*μ) (BΩ*X^2) ht₀ (by positivity)
    (mul_nonneg hBΩ (sq_nonneg X)) hωbound
  intro α σ hσ
  let t : Ioi (0:ℝ) := ⟨σ,ht₀.trans_le hσ⟩
  have hj : ‖D.w (j+1) t‖^2≤Cj*Real.exp (-2*μ*σ)*X^2 := by
    simpa only [D.initial,X] using hratej t hσ
  have hθ : |(α+D.theta σ)-(α+D.thetaLimit)|≤Bθ*Real.exp (-2*μ*σ)*X^2 := by
    rw [show (α+D.theta σ)-(α+D.thetaLimit)=D.theta σ-D.thetaLimit by ring,abs_sub_comm]
    have he : Real.exp (-(2*μ)*σ)=Real.exp (-2*μ*σ) := congrArg Real.exp (by ring)
    exact (htail σ hσ).trans_eq (by rw [he]; dsimp only [Bθ]; ring)
  have he := hEstimate (D.w (j+1) t) (α+D.theta σ) (α+D.thetaLimit) σ μ X hμ
    (ht₀.trans_le hσ).le hX hj hθ
  change periodicCjNorm j (fun s : ℝ => Complex.exp (((α+D.theta σ):ℂ)*I)*
      (B (Real.sqrt 2*s)+circleSobolevH1Embedding T
        (circleSobolevInclusion T 1 (D.u (Real.toNNReal σ)))
          ((Real.sqrt 2*s):AddCircle T)*N (Real.sqrt 2*s))-
      Complex.exp (((α+D.thetaLimit):ℂ)*I)*B (Real.sqrt 2*s))≤
    C*Real.exp (-μ*σ)*‖x₀‖
  simpa only [graph_height_jet T D.u D.w D.positiveValue j t,graph_rotation_exp,
    B,N,X,Function.comp_def,t,
    Real.toNNReal_of_nonneg (ht₀.trans_le hσ).le,Complex.ofReal_add] using! he

private abbrev GraphRateProperty
    (T : ℝ) [Fact (0<T)] (e : ℝ ≃o ℝ)
    (q p : C(AddCircle T,ℂ)) (ψ : CircleL2 T)
    (τ : ℝ) (hτ : 0<τ) (η : ℝ) (x₀ : CircleSobolevSpace T 2)
    (g : ℝ) (εRate CRate : Ioo (0:ℝ) g → ℕ → ℝ)
    (D : BernoulliNormalGraphEvolution T q p ψ τ hτ η x₀) : Prop :=
  ∀ μ : Ioo (0:ℝ) g,∀ j : ℕ,‖x₀‖≤εRate μ j →
    ∀ α σ : ℝ,Real.log 31/30≤σ →
      periodicCjNorm j (graphNormalizedError T e D.u D.theta D.thetaLimit α σ)≤
        CRate μ j*Real.exp (-(μ:ℝ)*σ)*‖x₀‖

private abbrev BernoulliPhysicalGraphProperty
    (T : ℝ) [Fact (0<T)] (e : ℝ ≃o ℝ)
    (q p : C(AddCircle T,ℂ)) (ψ : CircleL2 T)
    (τ : ℝ) (hτ : 0<τ) (η : ℝ) (x₀ : CircleSobolevSpace T 2)
    (h₀ : ℝ → ℝ) (g : ℝ) (εRate CRate : Ioo (0:ℝ) g → ℕ → ℝ)
    (D : BernoulliNormalGraphEvolution T q p ψ τ hτ η x₀) : Prop :=
  ∀ a : ℝ,0<a → ∀ p₀ : ℂ,∀ α : ℝ,
    let β := fun s : ℝ => bernoulliCurve (e.symm (Real.sqrt 2*s))
    let ν := fun s : ℝ => I*(bernoulliVelocity (e.symm (Real.sqrt 2*s))/
      (‖bernoulliVelocity (e.symm (Real.sqrt 2*s))‖:ℂ))
    let h := fun σ s : ℝ => (circleSobolevH1Embedding T
      (circleSobolevInclusion T 1 (D.u (Real.toNNReal σ)))) ((Real.sqrt 2*s):AddCircle T) |>.re
    ∃ ρ : ℝ → ℝ,ρ 0=a ∧
      (∀ t : ℝ,0≤t → 0<ρ t ∧ ρ t=(a^4+30*t)^(1/4:ℝ)) ∧
      Tendsto ρ atTop atTop ∧
      let Rlim := Complex.exp (((α+D.thetaLimit):ℂ)*I)
      let Y := fun t s : ℝ => p₀+(ρ t:ℂ)*
        (Complex.exp (((α+D.theta (normalizedTime a t)):ℂ)*I)*
          normalGraphCurve β ν (h (normalizedTime a t)) s)
      ‖Rlim‖=1 ∧
      (∀ s : ℝ,Y 0 s=p₀+(a:ℂ)*(Complex.exp ((α:ℂ)*I)*
        (β s+(h₀ (Real.sqrt 2*s):ℂ)*ν s))) ∧
      (∀ t : ℝ,0≤t → ContDiff ℝ ∞ (Y t)) ∧
      (∀ t : ℝ,0≤t → ∃ V : ℝ → ℂ,∀ s : ℝ,
        let n := I*deriv (Y t) s/(‖deriv (Y t) s‖:ℂ)
        HasDerivWithinAt (fun z => Y z s) (V s) (Ici (0:ℝ)) t ∧
        deriv (Y t) s≠0 ∧ ‖n‖=1 ∧
        (((conj (V s)*n).re:ℂ)*n)=
          -((arclengthDerivative (Y t)
            (arclengthDerivative (Y t) (planarSignedCurvature (Y t))) s+
            (1/2:ℝ)*(planarSignedCurvature (Y t) s)^3:ℝ):ℂ)*n) ∧
      (∀ j : ℕ,Tendsto (fun t : ℝ => periodicCjNorm j
        (fun s : ℝ => Y t s/(ρ t:ℂ)-Rlim*β s)) atTop (𝓝 0)) ∧
      ∀ μ : Ioo (0:ℝ) g,∀ j : ℕ,‖x₀‖≤εRate μ j →
        ∀ t : ℝ,a^4≤t → periodicCjNorm j
          (fun s : ℝ => (Y t s-p₀)/(ρ t:ℂ)-Rlim*β s)≤
            CRate μ j*(timeBase a t)^(-(μ:ℝ)/30)*‖x₀‖

private theorem graph_affine_division (p r z : ℂ) (hr : r≠0) :
    (p+r*z)/r=p/r+z ∧ (p+r*z-p)/r=z := by
  constructor
  · field_simp [hr]
  · field_simp [hr]
    ring

set_option maxHeartbeats 1200000 in
private theorem graph_evolution_physical_property
    (T : ℝ) [Fact (0<T)] (e : ℝ ≃o ℝ)
    (q p : C(AddCircle T,ℂ))
    (ψ : CircleL2 T) (δ : ℝ)
    (hPhysical : ∀ τ : ℝ,∀ hτ : 0<τ,∀ u : C(ℝ≥0,CircleSobolevSpace T 2),
      ∀ U : ℕ → CircleParabolicSpace T τ,∀ w : C(Ioi (0:ℝ),CircleSobolevSpace T 5),
      ∀ W₀ : C(unitInterval,CircleSobolevSpace T 5),∀ ω₁ : ℝ → ℝ,
      ∀ Ω₀ : C(unitInterval,ℝ),∀ θ : ℝ → ℝ,
      (∀ m,‖circleParabolicCurve T τ (U m)‖<δ) →
      (∀ m r,u (circleParabolicSegmentTime τ hτ m r)=circleParabolicCurve T τ (U m) r) →
      (∀ t : ℝ≥0,0<t → ∃ (m : ℕ) (r : unitInterval),
        0<(r:ℝ) ∧ (r:ℝ)<1 ∧ circleParabolicSegmentTime τ hτ m r=t) →
      (∀ t : Ioi (0:ℝ),circleSobolevInclusion T 2 (circleSobolevInclusion T 3
        (circleSobolevInclusion T 4 (w t)))=u ⟨(t:ℝ),t.property.le⟩) →
      (∀ r,circleSobolevInclusion T 2 (circleSobolevInclusion T 3
        (circleSobolevInclusion T 4 (W₀ r)))=circleParabolicCurve T τ (U 0) r) →
      (∀ t,circleSobolevConjugation T 2 (u t)=u t) →
      ContinuousOn ω₁ (Ioi (0:ℝ)) →
      (∀ t : Ioi (0:ℝ),(ω₁ t:ℂ)=circleNormalGraphAngularVelocity T
        (circleBernoulliBackground T q p) (15/2) ψ (circleSobolevInclusion T 4 (w t))) →
      (∀ r,(Ω₀ r:ℂ)=circleNormalGraphAngularVelocity T
        (circleBernoulliBackground T q p) (15/2) ψ (circleSobolevInclusion T 4 (W₀ r))) →
      ω₁ 0=Ω₀ 0 →
      (∀ m,∀ᵐ r ∂volume,circleParabolicTimeDerivative T τ (U m) r=
        circleNormalGraphModulatedFlow T (circleBernoulliBackground T q p) (15/2) ψ
          (circleParabolicH4 T τ (U m) r)) →
      (∀ σ : ℝ,0≤σ → HasDerivWithinAt θ (ω₁ σ) (Ici (0:ℝ)) σ) →
      ∀ a : ℝ,0<a → ∀ p₀ : ℂ,
      let φ := fun s : ℝ => e.symm (Real.sqrt 2*s)
      let β := bernoulliCurve ∘ φ
      let ν := fun s : ℝ => I*(bernoulliVelocity (φ s)/(‖bernoulliVelocity (φ s)‖:ℂ))
      let h := fun σ s : ℝ => (circleSobolevH1Embedding T
        (circleSobolevInclusion T 1 (u (Real.toNNReal σ)))) ((Real.sqrt 2*s):AddCircle T) |>.re
      ∃ ρ : ℝ → ℝ,ρ 0=a ∧
        (∀ t : ℝ,0≤t → 0<ρ t ∧ ρ t=(a^4+30*t)^(1/4:ℝ)) ∧
        Tendsto ρ atTop atTop ∧
        let Y := fun t s : ℝ => p₀+(ρ t:ℂ)*
          (Complex.exp ((θ (normalizedTime a t):ℂ)*I)*
            normalGraphCurve β ν (h (normalizedTime a t)) s)
        (∀ s,Y 0 s=p₀+(a:ℂ)*(Complex.exp ((θ 0:ℂ)*I)*normalGraphCurve β ν (h 0) s)) ∧
        ∀ t : ℝ,0≤t → ∃ V : ℝ → ℂ,∀ s : ℝ,
          let n := I*deriv (Y t) s/(‖deriv (Y t) s‖:ℂ)
          HasDerivWithinAt (fun z => Y z s) (V s) (Ici (0:ℝ)) t ∧
          deriv (Y t) s≠0 ∧ ‖n‖=1 ∧
          (((conj (V s)*n).re:ℂ)*n)=
            -((arclengthDerivative (Y t)
              (arclengthDerivative (Y t) (planarSignedCurvature (Y t))) s+
              (1/2:ℝ)*(planarSignedCurvature (Y t) s)^3:ℝ):ℂ)*n)
    (hβ : ContDiff ℝ ∞ (fun x : ℝ => bernoulliCurve (e.symm x)))
    (hβper : Function.Periodic (fun x : ℝ => bernoulliCurve (e.symm x)) T)
    (hν : ContDiff ℝ ∞ (fun x : ℝ => I*(bernoulliVelocity (e.symm x)/
      (‖bernoulliVelocity (e.symm x)‖:ℂ))))
    (hνper : Function.Periodic (fun x : ℝ => I*(bernoulliVelocity (e.symm x)/
      (‖bernoulliVelocity (e.symm x)‖:ℂ))) T)
    (τ : ℝ) (hτ : 0<τ) (x₀ : CircleSobolevSpace T 2)
    (h₀ : ℝ → ℝ) (hh₀ : ContDiff ℝ ∞ h₀)
    (h₀value : ∀ x : ℝ,circleSobolevH1Embedding T (circleSobolevInclusion T 1 x₀)
      (x:AddCircle T)=(h₀ x:ℂ))
    (g : ℝ) (εRate CRate : Ioo (0:ℝ) g → ℕ → ℝ)
    (D : BernoulliNormalGraphEvolution T q p ψ τ hτ δ x₀)
    (hRate : GraphRateProperty T e q p ψ τ hτ δ x₀ g εRate CRate D) :
    BernoulliPhysicalGraphProperty T e q p ψ τ hτ δ x₀ h₀ g εRate CRate D := by
  intro a ha p₀ α
  let Θ := fun σ : ℝ => α+D.theta σ
  have hΘ (σ : ℝ) (hσ : 0≤σ) : HasDerivWithinAt Θ (D.omega σ) (Ici (0:ℝ)) σ := by
    simpa only [zero_add,Θ,Pi.add_apply] using!
      (hasDerivWithinAt_const σ (Ici (0:ℝ)) α).add (D.thetaDerivative σ hσ)
  have hphysical := hPhysical τ hτ D.u D.U (D.w 5) D.initialLift D.omega D.initialOmega Θ
    (fun m => (graph_curve_norm T τ (D.U m)).trans_lt (D.segmentSmall m))
    D.segments (graph_interior_cover τ hτ) (graph_value_lift T D.u D.w D.positiveValue)
    D.initialValue D.real D.omegaContinuous D.omegaValue D.initialOmegaValue D.omegaZero
    D.equation hΘ a ha p₀
  dsimp only at hphysical ⊢
  refine graph_witness_transport hphysical ?_
  intro ρ hρdata
  obtain ⟨hρ₀,hρ,hρlim,hY₀,hYflow⟩ := hρdata
  let B := fun x : ℝ => bernoulliCurve (e.symm x)
  let N := fun x : ℝ => I*(bernoulliVelocity (e.symm x)/(‖bernoulliVelocity (e.symm x)‖:ℂ))
  let β := fun s : ℝ => B (Real.sqrt 2*s)
  let ν := fun s : ℝ => N (Real.sqrt 2*s)
  let h := fun σ s : ℝ => (circleSobolevH1Embedding T
    (circleSobolevInclusion T 1 (D.u (Real.toNNReal σ)))) ((Real.sqrt 2*s):AddCircle T) |>.re
  let Y := fun t s : ℝ => p₀+(ρ t:ℂ)*(Complex.exp ((Θ (normalizedTime a t):ℂ)*I)*
    normalGraphCurve β ν (h (normalizedTime a t)) s)
  have hheight₀ (s : ℝ) : h 0 s=h₀ (Real.sqrt 2*s) := by
    dsimp only [h]
    rw [Real.toNNReal_zero,D.initial,h₀value]
    exact Complex.ofReal_re _
  have hΘlim : Tendsto Θ atTop (𝓝 (α+D.thetaLimit)) :=
    tendsto_const_nhds.add D.thetaConvergence
  have hqual := normal_graph_global_cj_convergence T B N hβ hν hβper hνper D.u D.w
    D.positiveValue D.positiveLimit Θ (α+D.thetaLimit) hΘlim ρ hρlim p₀ a ha
  dsimp only at hqual
  refine ⟨ρ,hρ₀,hρ,hρlim,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Complex.ofReal_add] using Complex.norm_exp_ofReal_mul_I (α+D.thetaLimit)
  · intro s
    have hz := hY₀ s
    change Y 0 s=p₀+(a:ℂ)*(Complex.exp ((Θ 0:ℂ)*I)*normalGraphCurve β ν (h 0) s) at hz
    have hi : Y 0 s=p₀+(a:ℂ)*(Complex.exp ((α:ℂ)*I)*
        (β s+(h₀ (Real.sqrt 2*s):ℂ)*ν s)) := by
      rw [hz]
      simp only [Θ,D.thetaZero,add_zero,normalGraphCurve,hheight₀]
    simpa only [Y,Θ,B,N,β,ν,h,normalGraphCurve,Complex.ofReal_add] using! hi
  · intro t ht
    have hβs : ContDiff ℝ ∞ β := hβ.comp (contDiff_const.mul contDiff_id)
    have hνs : ContDiff ℝ ∞ ν := hν.comp (contDiff_const.mul contDiff_id)
    have hhs : ContDiff ℝ ∞ (fun s : ℝ => (h (normalizedTime a t) s:ℂ)) := by
      by_cases hσ : normalizedTime a t=0
      · have heq : (fun s : ℝ => (h (normalizedTime a t) s:ℂ))=
            fun s : ℝ => (h₀ (Real.sqrt 2*s):ℂ) := by
          funext s
          rw [hσ,hheight₀]
        rw [heq]
        exact Complex.ofRealCLM.contDiff.comp (hh₀.comp (contDiff_const.mul contDiff_id))
      · have hσnonneg : 0≤normalizedTime a t := by
          obtain ⟨_,hdata⟩ := physical_normalization a ha
          exact (hdata.2.2.1 t ht).2.2.1
        have hσpos : 0<normalizedTime a t := lt_of_le_of_ne hσnonneg (Ne.symm hσ)
        let σ : Ioi (0:ℝ) := ⟨normalizedTime a t,hσpos⟩
        have hc := graph_classical_height T D.u D.w D.positiveValue σ
        have hcc := hc.comp (contDiff_const.mul contDiff_id :
          ContDiff ℝ ∞ (fun s : ℝ => Real.sqrt 2*s))
        have heq : (fun s : ℝ => (h (normalizedTime a t) s:ℂ))=
            fun s : ℝ => circleSobolevH1Embedding T (circleSobolevInclusion T 1
              (D.u ⟨(σ:ℝ),σ.property.le⟩)) ((Real.sqrt 2*s):AddCircle T) := by
          funext s
          dsimp only [h,σ]
          rw [Real.toNNReal_of_nonneg hσpos.le]
          exact graph_h1_real T _ (D.real _) _
        rw [heq]
        exact hcc
    have hs : ContDiff ℝ ∞ (fun s : ℝ => p₀+(ρ t:ℂ)*
      (Complex.exp ((Θ (normalizedTime a t):ℂ)*I)*
        (β s+(h (normalizedTime a t) s:ℂ)*ν s))) :=
      contDiff_const.add (contDiff_const.mul
        (contDiff_const.mul (hβs.add (hhs.mul hνs))))
    simpa only [Θ,B,N,β,ν,h,normalGraphCurve,Complex.ofReal_add] using! hs
  · simpa only [Θ,Complex.ofReal_add,Function.comp_def] using! hYflow
  · intro j
    apply (hqual j).congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    have hρne : (ρ t:ℂ)≠0 := by exact_mod_cast (hρ t ht).1.ne'
    congr 1
    funext s
    let Z := Complex.exp ((Θ (normalizedTime a t):ℂ)*I)*
      (β s+circleSobolevH1Embedding T (circleSobolevInclusion T 1
        (D.u (Real.toNNReal (normalizedTime a t)))) ((Real.sqrt 2*s):AddCircle T)*ν s)
    have he : p₀/(ρ t:ℂ)+Z-Complex.exp (((α+D.thetaLimit):ℂ)*I)*β s=
        (p₀+(ρ t:ℂ)*Z)/(ρ t:ℂ)-Complex.exp (((α+D.thetaLimit):ℂ)*I)*β s := by
      rw [(graph_affine_division p₀ (ρ t:ℂ) Z hρne).1]
    simpa only [Z,Θ,Y,B,N,β,ν,h,normalGraphCurve,Complex.ofReal_add,
      graph_h1_real T _ (D.real _) ((Real.sqrt 2*s):AddCircle T)] using! he
  · intro μ j hx t ht
    have ht₀ : 0≤t := (pow_nonneg ha.le 4).trans ht
    have hρne : (ρ t:ℂ)≠0 := by exact_mod_cast (hρ t ht₀).1.ne'
    have he := hRate μ j hx α (normalizedTime a t)
      (normalizedTime_at_unit_scale a t ha ht)
    have herr : graphNormalizedError T e D.u D.theta D.thetaLimit α (normalizedTime a t)=
        fun s : ℝ => (Y t s-p₀)/(ρ t:ℂ)-Complex.exp (((α+D.thetaLimit):ℂ)*I)*β s := by
      funext s
      let Z := Complex.exp (((α+D.theta (normalizedTime a t)):ℂ)*I)*
        (β s+circleSobolevH1Embedding T (circleSobolevInclusion T 1
          (D.u (Real.toNNReal (normalizedTime a t)))) ((Real.sqrt 2*s):AddCircle T)*ν s)
      have hz : Z-Complex.exp (((α+D.thetaLimit):ℂ)*I)*β s=
          (p₀+(ρ t:ℂ)*Z-p₀)/(ρ t:ℂ)-Complex.exp (((α+D.thetaLimit):ℂ)*I)*β s := by
        rw [(graph_affine_division p₀ (ρ t:ℂ) Z hρne).2]
      simpa only [Z,graphNormalizedError,Y,Θ,B,N,β,ν,h,normalGraphCurve,Complex.ofReal_add,
        graph_h1_real T _ (D.real _) ((Real.sqrt 2*s):AddCircle T)] using! hz
    rw [herr,physical_decay_identity a t (μ:ℝ) ha ht₀] at he
    simpa only [Y,Θ,B,N,β,ν,h,normalGraphCurve,Complex.ofReal_add] using! he

variable (T S : ℝ) [Fact (0<T)] [Fact (0<S)]

set_option maxHeartbeats 1600000 in
/-- A small smooth real phase-fixed height produces one global physical
free elastic flow. The curve starts from the prescribed normal graph,
satisfies the projected equation also at the initial endpoint, and its
uncentered normalization converges in every spatial C^j norm to one
rotation of the Bernoulli lemniscate. The centered curve has every
subcritical spectral rate, with uniform radii and constants chosen before
the initial data, scale, center and initial angle. -/
theorem bernoulli_physical_graph_stability
    (e : ℝ ≃o ℝ)
    (he : ∀ u,e u=∫ t in (0:ℝ)..u,Real.sqrt 2*‖bernoulliVelocity t‖)
    (hT : T=e (2*Real.pi))
    (q p : C(AddCircle T,ℂ))
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
    (M : ℕ) (hM : 0<M) (hS : S=(M:ℝ)*T)
    (ηreq : ℝ) (hηreq : 0<ηreq) :
    let Q := circlePeriodicExtension T S M hS q
    let P := circlePeriodicExtension T S M hS p
    let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
    let g : ℝ := if M=1 then 21/4 else 1/(2*(M:ℝ)^2)
    ∃ τ : ℝ,∃ hτ : 0<τ,τ≤1 ∧ ∃ ε>0,
      ∃ εRate CRate : Ioo (0:ℝ) g → ℕ → ℝ,
      (∀ μ j,0<εRate μ j ∧ εRate μ j≤ε ∧ 0<CRate μ j) ∧
      ∀ x₀ : CircleSobolevSpace S 2,
      inner ℂ (Ψ:CircleL2 S) (circleSobolevCoordinate S 2 0 x₀)=0 → ‖x₀‖≤ε →
      ∀ h₀ : ℝ → ℝ,∀ hh₀ : ContDiff ℝ ∞ h₀,∀ hp₀ : Function.Periodic h₀ S,
      circleSobolevCoordinate S 2 0 x₀=circleContinuousL2 S
        (periodicCircleFunction S (fun x : ℝ => (h₀ x:ℂ))
          (fun x => congrArg Complex.ofReal (hp₀ x))
          (Complex.continuous_ofReal.comp hh₀.continuous)) →
      ∃ D : BernoulliNormalGraphEvolution S Q P (Ψ:CircleL2 S) τ hτ ηreq x₀,
        BernoulliPhysicalGraphProperty S e Q P (Ψ:CircleL2 S) τ hτ ηreq x₀ h₀ g εRate CRate D := by
  dsimp only
  let Q := circlePeriodicExtension T S M hS q
  let P := circlePeriodicExtension T S M hS p
  let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
  let K := circleBernoulliBackground S Q P
  let g : ℝ := if M=1 then 21/4 else 1/(2*(M:ℝ)^2)
  have hg : 0<g := by dsimp only [g]; split_ifs <;> positivity
  have hQ : HasCircleDeriv S Q P := circle_periodic_extension_deriv T S M hS q p hq
  have hP : HasCircleDeriv S P (-(Q^3)) := by
    simpa only [Q,map_neg,map_pow] using circle_periodic_extension_deriv T S M hS _ _ hp
  have hE' : ∀ x,2*(P x)^2+(Q x)^4=1 :=
    fun x => hE (circleCoverProjection T S M hS x)
  have hQreal : ∀ x,conj (Q x)=Q x := circle_periodic_extension_real T S M hS q hqreal
  have hPreal : ∀ x,conj (P x)=P x := circle_periodic_extension_real T S M hS p hpreal
  have hQstar : star Q=Q := ContinuousMap.ext hQreal
  have hPstar : star P=P := ContinuousMap.ext hPreal
  have hmul (a b : C(AddCircle S,ℂ)) : star (a*b)=star a*star b :=
    (starRingEnd C(AddCircle S,ℂ)).map_mul a b
  have hKstar : (⟨star K.k,star K.ks,star K.kss,star K.ksss,star K.eta,star K.b⟩ :
      BackgroundJetOver C(AddCircle S,ℂ))=K := by
    simp [K,circleBernoulliBackground,star_smul,hmul,hQstar,hPstar]
  have hstrong := bernoulli_cover_parabolic_smooth_stability T S q p hq hp hE
    hqreal hpreal hs hc ho hr ψ hnorm hψzero M hM hS
  dsimp only at hstrong
  obtain ⟨hΨ,hpair,τ,hτ,hτ₁,inv,hInverse,hsolve⟩ := hstrong
  have hsolve' : ∀ η>0,∃ r>0,r<η ∧ GraphSmallSolutionProperty S Q P
      (Ψ:CircleL2 S) τ hτ g r := hsolve
  have htame := (paper_periodic_cover_modulated_tame_data T S q p hq hp hE
    hqreal hpreal hs hc ho hr ψ hnorm hψzero M hM hS).2.2
  have hD : circleNormalGraphDerivative S K (15/2)=
      circleSobolevOperator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • Q^4) :=
    (circle_normal_graph_hasFDerivAt S K (15/2)).unique
      (bernoulli_sobolev_flow_linearization S Q P hE').2
  have hneutral (f : CircleSobolevSpace S 4) :
      circleNormalGraphRotationFunctional S (Ψ:CircleL2 S)
        (circleNormalGraphDerivative S K (15/2) f)=0 := by
    change inner ℂ (Ψ:CircleL2 S) (circleNormalGraphDerivative S K (15/2) f)=0
    rw [hD,circle_sobolev_operator_eq_h4]
    exact htame.2.2.1 (circleSobolevToH4Domain S f)
  have hQlift (x : ℝ) : Q (x:AddCircle S)=(bernoulliProfileQ (e.symm x):ℂ) := hqlift x
  have hPlift (x : ℝ) : P (x:AddCircle S)=(bernoulliProfileP (e.symm x):ℂ) := hplift x
  obtain ⟨hβ,hβper,hν,hνper⟩ :=
    bernoulli_reference_profile_geometry T S e he hT q p hq hqlift M hS (Ψ:CircleL2 S) hpair
  refine graph_positive_transport
    (bernoulli_physical_normal_graph_flow S e he Q P hQlift hPlift (Ψ:CircleL2 S)) ?_
  intro δ hδ hPhysical
  refine graph_two_positive_transport
    (circle_normal_graph_angular_velocity_bound S K (15/2) (Ψ:CircleL2 S) hpair
      (bernoulli_sobolev_flow_linearization S Q P hE').1 hneutral).2 ?_
  intro δΩ hδΩ CΩ hCΩ hΩ
  refine graph_positive_transport (hsolve' ηreq hηreq) ?_
  intro ηA hηA hA
  let ηB := min ηA (min δ δΩ)
  have hηB : 0<ηB := lt_min hηA (lt_min hδ hδΩ)
  refine graph_positive_transport
    (graph_evolution_of_small_solutions S Q P hQ hP hE' (Ψ:CircleL2 S) hΨ hpair hKstar
      hneutral τ hτ inv hInverse g hg hsolve' ηB hηB) ?_
  intro ε hε hEvolution
  have ht₀ : 0<Real.log 31/30 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  choose εRaw hεRaw CRaw hCRaw hRaw using fun (μ : Ioo (0:ℝ) g) (j : ℕ) =>
    graph_uniform_convergence_rate S e Q P (Ψ:CircleL2 S) τ hτ g ηA ηB δΩ CΩ
      (min_le_left _ _) ((min_le_right _ _).trans (min_le_right _ _)) hCΩ hA.2
      (fun f hf => (hΩ f hf).2) hβ hβper hν hνper (Real.log 31/30) (μ:ℝ)
      ht₀ μ.property.1 μ.property.2 j
  let εRate := fun (μ : Ioo (0:ℝ) g) (j : ℕ) => min ε (εRaw μ j)
  refine ⟨τ,hτ,hτ₁,ε,hε,εRate,CRaw,?_,?_⟩
  · intro μ j
    exact ⟨lt_min hε (hεRaw μ j),min_le_left _ _,hCRaw μ j⟩
  intro x₀ hphase hsmall h₀ hh₀ hp₀ hvalue
  let f₀ : C(AddCircle S,ℂ) := periodicCircleFunction S (fun x : ℝ => (h₀ x:ℂ))
    (fun x => congrArg Complex.ofReal (hp₀ x))
    (Complex.continuous_ofReal.comp hh₀.continuous)
  have hf₀ (x : ℝ) : f₀ (x:AddCircle S)=(h₀ x:ℂ) := rfl
  have hf₀star : star f₀=f₀ := by
    ext x
    refine QuotientAddGroup.induction_on x ?_
    intro x
    exact Complex.conj_ofReal _
  have hreal : circleSobolevConjugation S 2 x₀=x₀ := by
    apply circle_sobolev_value_injective S 2
    rw [circle_sobolev_conjugation_coordinate,hvalue,← circle_continuous_l2_star,hf₀star]
  have hheight₀ : circleSobolevH1Embedding S (circleSobolevInclusion S 1 x₀)=f₀ := by
    apply ContinuousMap.toLp_injective (p:=2) (𝕜:=ℂ) AddCircle.haarAddCircle
    change circleContinuousL2 S _=circleContinuousL2 S _
    rw [circle_sobolev_h1_embedding_l2]
    exact hvalue
  have hh₀C : ContDiff ℝ ∞ (fun x : ℝ => (h₀ x:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hh₀
  obtain ⟨F,hFpoint,hF⟩ := periodic_smooth_classical_jet S
    (fun x : ℝ => (h₀ x:ℂ)) hh₀C (fun x => congrArg Complex.ofReal (hp₀ x))
  have hF₀ : F 0=f₀ := by
    ext x
    refine QuotientAddGroup.induction_on x ?_
    intro x
    rw [hf₀]
    simpa only [iteratedDeriv_zero] using hFpoint 0 x
  let Dlow := Classical.choice (hEvolution x₀ hreal hphase hsmall F hF (by rw [hF₀]; exact hvalue))
  let D : BernoulliNormalGraphEvolution S Q P (Ψ:CircleL2 S) τ hτ ηreq x₀ :=
    { Dlow with segmentSmall := fun m =>
        ((Dlow.segmentSmall m).trans_le (min_le_left _ _)).trans hA.1 }
  let Dδ : BernoulliNormalGraphEvolution S Q P (Ψ:CircleL2 S) τ hτ δ x₀ :=
    { Dlow with segmentSmall := fun m =>
        (Dlow.segmentSmall m).trans_le ((min_le_right _ _).trans (min_le_left _ _)) }
  have hRate : GraphRateProperty S e Q P (Ψ:CircleL2 S) τ hτ δ x₀ g εRate CRaw Dδ := by
    intro μ j hx α σ hσ
    exact hRaw μ j x₀ Dlow (hx.trans (min_le_right _ _)) α σ hσ
  refine ⟨D,?_⟩
  have hproperty := graph_evolution_physical_property S e Q P (Ψ:CircleL2 S)
    δ hPhysical hβ hβper hν hνper τ hτ x₀ h₀ hh₀
    (fun x => by rw [hheight₀]; exact hf₀ x) g εRate CRaw Dδ hRate
  exact hproperty

end Lemniscate
