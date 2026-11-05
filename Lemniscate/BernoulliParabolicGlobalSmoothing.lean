import Lemniscate.BernoulliParabolicSmoothing
import Lemniscate.NormalGraphParabolicAngularVelocity
import Lemniscate.PeriodicParabolicGlobalRegularity

/-! Positive-time spatial regularity of the actual overlapping modulated
solution. The same small MR neighbourhood works for every Sobolev order.
The quantitative part takes only the H2 decay and the segment H4 bound
which are supplied by the already proved energy estimate.
 -/

noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal Topology NNReal

variable (T : ℝ) [Fact (0 < T)]

private theorem global_smoothing_component_bounds
    (τ : ℝ) (U : CircleParabolicSpace T τ) :
    ‖circleParabolicCurve T τ U‖ ≤ ‖U‖ ∧
      ‖circleParabolicH4 T τ U‖ ≤ ‖U‖ ∧
      ‖circleParabolicInitialValue T τ U‖ ≤ ‖circleParabolicCurve T τ U‖ := by
  constructor
  · change ‖U.val.1‖ ≤ ‖U.val‖
    exact norm_fst_le U.val
  constructor
  · change ‖U.val.2.1‖ ≤ ‖U.val‖
    exact (norm_fst_le U.val.2).trans (norm_snd_le U.val)
  · exact (circleParabolicCurve T τ U).norm_coe_le_norm 0

private theorem global_smoothing_data_small
    (s η C a b d : ℝ) (hs : 0 < s) (hC : 0 ≤ C)
    (hη1 : η ≤ 1) (hηs : η ≤ s/(2*(1+C)))
    (ha : a < η) (hb : b ≤ η) (hd : d ≤ C*a*b)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) : a+d < s := by
  have hden : 0 < 2*(1+C) := by positivity
  have hηbound : η*(2*(1+C)) ≤ s := (le_div_iff₀ hden).mp hηs
  have hd' : d ≤ C*η := by
    calc
      d ≤ C*a*b := hd
      _ ≤ C*η*b := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ha.le hC) hb0
      _ ≤ C*η := by
        have hη0 : 0 ≤ η := ha0.trans ha.le
        exact mul_le_of_le_one_right (mul_nonneg hC hη0) (hb.trans hη1)
  nlinarith only [ha,hd',hηbound,hs]

private theorem global_smoothing_data_bound
    (C η A a b d x : ℝ) (hC : 0 ≤ C) (hη : 0 ≤ η) (hA : 0 ≤ A)
    (ha : a ≤ η) (hb : b ≤ A*x) (hd : d ≤ C*a*b)
    (hb0 : 0 ≤ b) : x+d ≤ (1+C*η*A)*x := by
  have h : d ≤ C*η*(A*x) := by
    calc
      d ≤ C*a*b := hd
      _ ≤ C*η*b := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ha hC) hb0
      _ ≤ C*η*(A*x) := mul_le_mul_of_nonneg_left hb (mul_nonneg hC hη)
  nlinarith only [h]

private theorem global_smoothing_initial_decay
    (τ : ℝ) (hτ : 0 < τ) (μ D : ℝ)
    (u : C(ℝ≥0,CircleSobolevSpace T 2))
    (U : ℕ → CircleParabolicSpace T τ)
    (hrep : ∀ m r, u (circleParabolicSegmentTime τ hτ m r) =
      circleParabolicCurve T τ (U m) r)
    (hdecay : ∀ t : ℝ≥0, ‖u t‖ ≤ D*Real.exp (-μ*(t:ℝ))*‖u 0‖)
    (m : ℕ) :
    ‖circleParabolicInitialValue T τ (U m)‖ ≤
      D*Real.exp (-μ*(τ*((m:ℝ)/2)))*‖u 0‖ := by
  have hi : circleParabolicInitialValue T τ (U m) =
      u (circleParabolicSegmentTime τ hτ m 0) := (hrep m 0).symm
  have h := hdecay (circleParabolicSegmentTime τ hτ m 0)
  change ‖u (circleParabolicSegmentTime τ hτ m 0)‖ ≤
    D*Real.exp (-μ*(τ*((m:ℝ)/2+(0:ℝ))))*‖u 0‖ at h
  exact (congrArg (fun y : CircleSobolevSpace T 2 => ‖y‖) hi).le.trans
    (by simpa only [add_zero] using! h)

private theorem global_smoothing_exponential_shift
    (τ μ s t r : ℝ) (hτ : 0 ≤ τ) (hμ : 0 ≤ μ)
    (hr : r ≤ 1) (ht : s+τ*r = t) :
    (Real.exp (-μ*s))^2 ≤ Real.exp (2*μ*τ)*Real.exp (-2*μ*t) := by
  have hst : t-τ ≤ s := by nlinarith only [mul_le_mul_of_nonneg_left hr hτ,ht]
  calc
    (Real.exp (-μ*s))^2 = Real.exp (-2*μ*s) := by
      rw [pow_two,← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (2*μ*τ+(-2*μ*t)) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hst hμ
      nlinarith only [hmul]
    _ = Real.exp (2*μ*τ)*Real.exp (-2*μ*t) := Real.exp_add _ _

private theorem global_smoothing_radius_transport {P : ℝ → Prop} {Q : Prop}
    (h : ∃ a > 0, P a) (k : ∀ a, 0 < a → P a → Q) : Q := by
  obtain ⟨a,ha,hP⟩ := h
  exact k a ha hP

private theorem global_smoothing_two_radius_transport {P : ℝ → ℝ → Prop} {Q : Prop}
    (h : ∃ a > 0, ∃ b > 0, P a b)
    (k : ∀ a, 0 < a → ∀ b, 0 < b → P a b → Q) : Q := by
  obtain ⟨a,ha,b,hb,hP⟩ := h
  exact k a ha b hb hP

private theorem global_smoothing_witness_transport {X : Type*} {P : X → Prop} {Q : Prop}
    (h : ∃ x, P x) (k : ∀ x, P x → Q) : Q := by
  obtain ⟨x,hx⟩ := h
  exact k x hx

set_option maxHeartbeats 1200000 in
/-- A common MR neighbourhood gives every positive-time Sobolev order
for the same global solution. Its higher norm has the same exponential
rate whenever the H2 decay and the segment H4 energy bound hold. The
quantitative constants precede the choice of the global solution; the
bound applies to any representative of its value coordinate. -/
theorem bernoulli_parabolic_global_smoothing
    (q p : C(AddCircle T, ℂ)) (hq : HasCircleDeriv T q p)
    (hp : HasCircleDeriv T p (-(q^3))) (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (τ : ℝ) (hτ : 0 < τ)
    (e : CircleParabolicSpace T τ ≃L[ℂ] (CircleSobolevSpace T 2 × CircleTimeL2 T))
    (heInverse : e.toContinuousLinearMap = circleParabolicLowerOrderData T τ
      (circleSobolevCoordinate T 2 0+
        circleSobolevLowerOrderOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))))
    (ψ : CircleL2 T)
    (hpair : inner ℂ ψ (circleContinuousL2 T (circleBernoulliBackground T q p).b) ≠ 0)
    (hFzero : circleNormalGraphFlow T (circleBernoulliBackground T q p) (15/2) 0 = 0)
    (hneutral : ∀ f : CircleSobolevSpace T 4,
      circleNormalGraphRotationFunctional T ψ
        (circleNormalGraphDerivative T (circleBernoulliBackground T q p) (15/2) f) = 0) :
    ∃ η > 0,
      (∀ (u : C(ℝ≥0,CircleSobolevSpace T 2)) (U : ℕ → CircleParabolicSpace T τ),
        (∀ m r, u (circleParabolicSegmentTime τ hτ m r) =
          circleParabolicCurve T τ (U m) r) →
        (∀ m, ‖U m‖ < η) →
        (∀ m, ∀ᵐ t ∂volume, circleParabolicTimeDerivative T τ (U m) t =
          circleNormalGraphModulatedFlow T (circleBernoulliBackground T q p) (15/2) ψ
            (circleParabolicH4 T τ (U m) t)) →
        ∃ v : ∀ n : ℕ, C(Ioi (0:ℝ),CircleSobolevSpace T n),
          ∀ n (t : Ioi (0:ℝ)), circleSobolevCoordinate T n 0 (v n t) =
            circleSobolevCoordinate T 2 0 (u ⟨(t:ℝ),t.property.le⟩)) ∧
      (∀ A > 0, ∀ D > 0, ∀ μ > 0, ∀ n : ℕ, ∀ t₀ > 0,
        ∃ ε > 0, ∃ C > 0,
        ∀ (u : C(ℝ≥0,CircleSobolevSpace T 2)) (U : ℕ → CircleParabolicSpace T τ),
          (∀ m r, u (circleParabolicSegmentTime τ hτ m r) =
            circleParabolicCurve T τ (U m) r) →
          (∀ m, ‖U m‖ < η) →
          (∀ m, ∀ᵐ t ∂volume, circleParabolicTimeDerivative T τ (U m) t =
            circleNormalGraphModulatedFlow T (circleBernoulliBackground T q p) (15/2) ψ
              (circleParabolicH4 T τ (U m) t)) →
          (∀ m, ‖circleParabolicH4 T τ (U m)‖ ≤
            A*‖circleParabolicInitialValue T τ (U m)‖) →
          (∀ t : ℝ≥0, ‖u t‖ ≤ D*Real.exp (-μ*(t:ℝ))*‖u 0‖) →
          ∀ v : C(Ioi (0:ℝ),CircleSobolevSpace T n),
            (∀ t : Ioi (0:ℝ), circleSobolevCoordinate T n 0 (v t) =
              circleSobolevCoordinate T 2 0 (u ⟨(t:ℝ),t.property.le⟩)) →
            ∀ t : Ioi (0:ℝ), t₀ ≤ (t:ℝ) →
              D*Real.exp (-μ*((t:ℝ)-τ))*‖u 0‖ < ε →
              ‖v t‖^2 ≤ C*Real.exp (-2*μ*(t:ℝ))*‖u 0‖^2) := by
  refine global_smoothing_radius_transport
    (bernoulli_parabolic_smoothing T q p hq hp he τ hτ.ne' e heInverse) ?_
  intro s hs hregularity
  have hqual := hregularity.1
  have hquant := hregularity.2
  refine global_smoothing_two_radius_transport
    (circle_parabolic_normal_graph_angular_velocity T
      (circleBernoulliBackground T q p) (15/2) ψ hpair hFzero hneutral) ?_
  intro d hd CΩ hCΩ hangular
  let η : ℝ := min d (min 1 (min s (s/(2*(1+CΩ)))))
  have hη : 0 < η := lt_min hd (lt_min (by norm_num)
    (lt_min hs (div_pos hs (by positivity))))
  have hηd : η ≤ d := min_le_left _ _
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hηs : η ≤ s :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hηq : η ≤ s/(2*(1+CΩ)) :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hsegment (U : CircleParabolicSpace T τ) (hU : ‖U‖ < η)
      (hPDE : ∀ᵐ t ∂volume, circleParabolicTimeDerivative T τ U t =
        circleNormalGraphModulatedFlow T (circleBernoulliBackground T q p) (15/2) ψ
          (circleParabolicH4 T τ U t)) :
      ∃ φ : Lp ℂ 2 (volume : Measure unitInterval),
        ‖φ‖ ≤ CΩ*‖circleParabolicCurve T τ U‖*‖circleParabolicH4 T τ U‖ ∧
        ‖circleParabolicInitialValue T τ U‖+‖φ‖ < s ∧
        (∀ᵐ t ∂volume, circleParabolicTimeDerivative T τ U t =
          circleNormalGraphFlow T (circleBernoulliBackground T q p) (15/2)
            (circleParabolicH4 T τ U t)-
          φ t • circleNormalGraphRotationField T (circleBernoulliBackground T q p)
            (circleParabolicCurve T τ U t)) := by
    have hcomp := global_smoothing_component_bounds T τ U
    have hcη := hcomp.1.trans_lt hU
    refine global_smoothing_witness_transport (hangular τ U (hcη.trans_le hηd)) ?_
    intro φ hangularData
    have hφ := hangularData.2.1
    have hraw := hangularData.2.2
    have hn4 := norm_nonneg (circleParabolicH4 T τ U)
    refine ⟨φ,hφ,?_,hraw hPDE⟩
    have hsmall : ‖circleParabolicCurve T τ U‖+‖φ‖ < s :=
      global_smoothing_data_small s η CΩ ‖circleParabolicCurve T τ U‖
        ‖circleParabolicH4 T τ U‖ ‖φ‖ hs hCΩ.le hη1 hηq hcη
        (hcomp.2.1.trans hU.le) hφ (norm_nonneg (circleParabolicCurve T τ U)) hn4
    have hadd : ‖circleParabolicInitialValue T τ U‖+‖φ‖ ≤
        ‖circleParabolicCurve T τ U‖+‖φ‖ := add_le_add hcomp.2.2 (le_refl ‖φ‖)
    exact hadd.trans_lt hsmall
  refine ⟨η,hη,?_,?_⟩
  · intro u U hrep hsmall hPDE
    have hreg (n : ℕ) : ∃ v : C(Ioi (0:ℝ),CircleSobolevSpace T n),
        ∀ t : Ioi (0:ℝ), circleSobolevCoordinate T n 0 (v t) =
          circleSobolevCoordinate T 2 0 (u ⟨(t:ℝ),t.property.le⟩) := by
      apply circle_parabolic_global_sobolev_lift T τ hτ n u U hrep
      intro m r₀ hr₀
      obtain ⟨φ,_,hdata,hraw⟩ := hsegment (U m) (hsmall m) (hPDE m)
      exact hqual (U m) ((hsmall m).trans_le hηs) φ hdata hraw n r₀ hr₀
    choose v hv using hreg
    exact ⟨v,hv⟩
  · intro A hA D hD μ hμ n t₀ ht₀
    let r₀ : ℝ := min (1/2:ℝ) (t₀/τ)
    have hr₀ : 0 < r₀ := lt_min (by norm_num) (div_pos ht₀ hτ)
    refine global_smoothing_radius_transport (hquant n r₀ hr₀) ?_
    intro ε₀ hε₀ hlocalData
    refine global_smoothing_radius_transport hlocalData.2 ?_
    intro C₀ hC₀ hlocal
    let B : ℝ := 1+CΩ*η*A
    have hB : 0 < B := by dsimp only [B]; positivity
    let ε : ℝ := ε₀/(B+1)
    let C : ℝ := C₀*(B*D)^2*Real.exp (2*μ*τ)
    have hε : 0 < ε := div_pos hε₀ (by positivity)
    have hC : 0 < C := by dsimp only [C]; positivity
    refine ⟨ε,hε,C,hC,?_⟩
    intro u U hrep hsmall hPDE hH4 hdecay v hv t ht hx
    obtain ⟨m,r,_,hrlo,htr⟩ :=
      circle_parabolic_interior_time τ hτ t₀ ht₀ ⟨(t:ℝ),t.property.le⟩ ht
    obtain ⟨φ,hφ,_,hraw⟩ := hsegment (U m) (hsmall m) (hPDE m)
    have hcomp := global_smoothing_component_bounds T τ (U m)
    have hn4 := norm_nonneg (circleParabolicH4 T τ (U m))
    have hdata : ‖circleParabolicInitialValue T τ (U m)‖+‖φ‖ ≤
        B*‖circleParabolicInitialValue T τ (U m)‖ :=
      global_smoothing_data_bound CΩ η A ‖circleParabolicCurve T τ (U m)‖
        ‖circleParabolicH4 T τ (U m)‖ ‖φ‖
        ‖circleParabolicInitialValue T τ (U m)‖ hCΩ.le hη.le hA.le
        (hcomp.1.trans (hsmall m).le) (hH4 m) hφ hn4
    let start : ℝ := τ*((m:ℝ)/2)
    have hi : ‖circleParabolicInitialValue T τ (U m)‖ ≤
        D*Real.exp (-μ*start)*‖u 0‖ :=
      global_smoothing_initial_decay T τ hτ μ D u U hrep hdecay m
    have htime : start+τ*(r:ℝ) = (t:ℝ) := by
      have htr' := congrArg (fun y : ℝ≥0 => (y:ℝ)) htr
      change τ*((m:ℝ)/2+(r:ℝ)) = (t:ℝ) at htr'
      dsimp only [start]
      nlinarith only [htr']
    have hstart : (t:ℝ)-τ ≤ start := by
      have hmul := mul_le_mul_of_nonneg_left r.property.2 hτ.le
      nlinarith only [htime,hmul]
    have hinit : ‖circleParabolicInitialValue T τ (U m)‖ ≤
        D*Real.exp (-μ*((t:ℝ)-τ))*‖u 0‖ := by
      have hexp : Real.exp (-μ*start) ≤ Real.exp (-μ*((t:ℝ)-τ)) := by
        apply Real.exp_le_exp.mpr
        have hmul := mul_le_mul_of_nonneg_left hstart hμ.le
        nlinarith only [hmul]
      calc
        ‖circleParabolicInitialValue T τ (U m)‖ ≤
            D*Real.exp (-μ*start)*‖u 0‖ := hi
        _ ≤ D*Real.exp (-μ*((t:ℝ)-τ))*‖u 0‖ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp hD.le) (norm_nonneg _)
    have hdsmall : ‖circleParabolicInitialValue T τ (U m)‖+‖φ‖ < ε₀ := by
      have hx' : (D*Real.exp (-μ*((t:ℝ)-τ))*‖u 0‖)*(B+1) < ε₀ :=
        (lt_div_iff₀ (by positivity)).mp hx
      calc
        ‖circleParabolicInitialValue T τ (U m)‖+‖φ‖ ≤
            B*‖circleParabolicInitialValue T τ (U m)‖ := hdata
        _ ≤ B*(D*Real.exp (-μ*((t:ℝ)-τ))*‖u 0‖) :=
          mul_le_mul_of_nonneg_left hinit hB.le
        _ ≤ (D*Real.exp (-μ*((t:ℝ)-τ))*‖u 0‖)*(B+1) := by
          have hnonneg : 0 ≤ D*Real.exp (-μ*((t:ℝ)-τ))*‖u 0‖ := by positivity
          nlinarith only [hnonneg]
        _ < ε₀ := hx'
    obtain ⟨w,hw⟩ := hlocal (U m) ((hsmall m).trans_le hηs) φ hdsmall hraw
    let z : Icc r₀ (1:ℝ) := ⟨(r:ℝ),hrlo,r.property.2⟩
    have hc : circleParabolicCurve T τ (U m) r = u ⟨(t:ℝ),t.property.le⟩ :=
      (hrep m r).symm.trans (congrArg u htr)
    have heq : v t = w z := by
      apply circle_sobolev_value_injective T n
      exact (hv t).trans (((hw z).1.trans
        (congrArg (circleSobolevCoordinate T 2 0) hc)).symm)
    have hshift := global_smoothing_exponential_shift τ μ start (t:ℝ) (r:ℝ)
      hτ.le hμ.le r.property.2 htime
    calc
      ‖v t‖^2 = ‖w z‖^2 := congrArg (fun y : CircleSobolevSpace T n => ‖y‖^2) heq
      _ ≤ C₀*(‖circleParabolicInitialValue T τ (U m)‖+‖φ‖)^2 := (hw z).2
      _ ≤ C₀*(B*‖circleParabolicInitialValue T τ (U m)‖)^2 :=
        mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ (by positivity) (by positivity)).2 hdata) hC₀.le
      _ ≤ C₀*(B*(D*Real.exp (-μ*start)*‖u 0‖))^2 :=
        mul_le_mul_of_nonneg_left ((sq_le_sq₀ (by positivity) (by positivity)).2
          (mul_le_mul_of_nonneg_left hi hB.le)) hC₀.le
      _ = (C₀*(B*D)^2*‖u 0‖^2)*(Real.exp (-μ*start))^2 := by ring
      _ ≤ (C₀*(B*D)^2*‖u 0‖^2)*
          (Real.exp (2*μ*τ)*Real.exp (-2*μ*(t:ℝ))) :=
        mul_le_mul_of_nonneg_left hshift (by positivity)
      _ = C*Real.exp (-2*μ*(t:ℝ))*‖u 0‖^2 := by dsimp only [C]; ring

end Lemniscate
