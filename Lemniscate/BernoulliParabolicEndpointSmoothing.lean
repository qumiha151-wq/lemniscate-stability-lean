import Lemniscate.BernoulliParabolicEndpointTranslation
import Lemniscate.PeriodicSobolevNonvanishingTranslation
import Lemniscate.PeriodicClassicalTranslationSmoothness

/-! Spatial smoothness extends continuously to the initial endpoint for
smooth initial data. The permitted H2/parabolic neighbourhood is independent
of every higher norm of that initial datum. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff

private theorem endpoint_branch_transport {P X : Type*} {A : ℝ → ℝ → (P → X) → Prop} {Q : Prop}
    (h : ∃ ε > 0, ∃ r > 0, ∃ g : P → X, A ε r g)
    (k : ∀ ε, 0 < ε → ∀ r, 0 < r → ∀ g : P → X, A ε r g → Q) : Q := by
  obtain ⟨ε,hε,r,hr,g,hA⟩ := h
  exact k ε hε r hr g hA

private theorem endpoint_one_radius_transport {P : ℝ → Prop} {Q : Prop}
    (h : ∃ δ > 0, P δ) (k : ∀ δ, 0 < δ → P δ → Q) : Q := by
  obtain ⟨δ,hδ,hP⟩ := h
  exact k δ hδ hP

variable (T : ℝ) [Fact (0 < T)]

private theorem endpoint_l2_zero (f : CircleL2 T) : circleL2Translation T 0 f = f := by
  apply circle_fourier_ext T
  intro n
  rw [circle_l2_translation_fourier,fourier_eval_zero,one_mul]

private theorem endpoint_translation_zero (τ : ℝ) (hτ : τ ≠ 0)
    (U : CircleParabolicSpace T τ) : circleParabolicEndpointTranslation T τ hτ 0 U = U := by
  let V := circleParabolicEndpointTranslation T τ hτ 0 U
  have hcomp := circle_parabolic_endpoint_translation_components T τ hτ 0 U
  have hc : circleParabolicCurve T τ V = circleParabolicCurve T τ U := by
    apply ContinuousMap.ext
    intro t
    simpa only [zero_mul,AddCircle.coe_zero,circle_sobolev_translation_zero] using
      circle_parabolic_endpoint_translation_curve T τ hτ 0 U t
  have hh : circleParabolicH4 T τ V = circleParabolicH4 T τ U := by
    apply Lp.ext
    exact hcomp.1.mono (fun _ h => by
      simpa only [zero_mul,AddCircle.coe_zero,circle_sobolev_translation_zero] using h)
  have hv : circleParabolicTimeDerivative T τ V = circleParabolicTimeDerivative T τ U := by
    apply Lp.ext
    exact hcomp.2.1.mono (fun _ h => by
      simpa only [zero_mul,AddCircle.coe_zero,zero_div,Complex.ofReal_zero,zero_smul,
        add_zero,endpoint_l2_zero] using h)
  apply Subtype.ext
  exact Prod.ext hc (Prod.ext hh hv)

set_option synthInstance.maxHeartbeats 80000 in
private def endpointValueCurve (τ : ℝ) :
    CircleParabolicSpace T τ →L[ℝ] C(unitInterval,CircleL2 T) :=
  (((circleSobolevCoordinate T 2 0).compLeftContinuous ℂ unitInterval).comp
    (circleParabolicCurve T τ)).restrictScalars ℝ

set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 1000000 in
/-- For an actual solution with a smooth classical initial height, all
spatial Sobolev orders are continuous on the entire closed unit interval.
One small low-order neighbourhood works for every order. -/
theorem bernoulli_parabolic_endpoint_smoothing
    (q p : C(AddCircle T,ℂ)) (hq : HasCircleDeriv T q p)
    (hp : HasCircleDeriv T p (-(q^3))) (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (τ : ℝ) (hτ : τ ≠ 0)
    (e : CircleParabolicSpace T τ ≃L[ℂ] (CircleSobolevSpace T 2 × CircleTimeL2 T))
    (heInverse : e.toContinuousLinearMap = circleParabolicLowerOrderData T τ
      (circleSobolevCoordinate T 2 0+
        circleSobolevLowerOrderOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)))) :
    ∃ η > 0, ∀ U : CircleParabolicSpace T τ, ‖U‖ < η →
      ∀ φ : Lp ℂ 2 (volume : Measure unitInterval),
      ‖circleParabolicInitialValue T τ U‖+‖φ‖ < η →
      (∀ᵐ t ∂volume, circleParabolicTimeDerivative T τ U t =
        circleNormalGraphFlow T (circleBernoulliBackground T q p) (15/2) (circleParabolicH4 T τ U t)-
          φ t • circleNormalGraphRotationField T (circleBernoulliBackground T q p)
            (circleParabolicCurve T τ U t)) →
      ∀ f : ℕ → C(AddCircle T,ℂ),
      (∀ j, HasCircleDeriv T (f j) (f (j+1))) →
      circleSobolevCoordinate T 2 0 (circleParabolicInitialValue T τ U) =
        circleContinuousL2 T (f 0) →
      ∀ n : ℕ, ∃ v : C(unitInterval,CircleSobolevSpace T n),
        ∀ t : unitInterval, circleSobolevCoordinate T n 0 (v t) =
          circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ U t) := by
  refine endpoint_branch_transport
    (bernoulli_parabolic_endpoint_implicit_solution T q p hq hp he τ e heInverse) ?_
  intro ε hε r hr g hbranch
  refine endpoint_one_radius_transport (bernoulli_parabolic_endpoint_translation_equation T q p) ?_
  intro δ hδ htranslated
  let η := min δ (min r ε)
  have hη : 0 < η := lt_min hδ (lt_min hr hε)
  refine ⟨η,hη,?_⟩
  intro U hU φ hdata hPDE f hf hvalue n
  let I := circleParabolicInitialValue T τ U
  let z : ℝ → CircleParabolicParameter T := fun a =>
    (a,circleSobolevTranslation T 2 (a:AddCircle T) I,φ)
  let V : ℝ → CircleParabolicSpace T τ := fun a => circleParabolicEndpointTranslation T τ hτ a U
  have hz : ContDiff ℝ ∞ z :=
    contDiff_id.prodMk ((circle_sobolev_translation_smooth_of_classical_jet T 2 I f hf hvalue).prodMk
      contDiff_const)
  have hz0 : ‖z 0‖ < ε := by
    have hh : max ‖I‖ ‖φ‖ ≤ ‖I‖+‖φ‖ :=
      max_le (le_add_of_nonneg_right (norm_nonneg φ))
        (le_add_of_nonneg_left (norm_nonneg I))
    have hhε := hdata.trans_le ((min_le_right δ (min r ε)).trans (min_le_right r ε))
    simpa only [z,zero_add,AddCircle.coe_zero,circle_sobolev_translation_zero,
      Prod.norm_def,norm_zero,max_eq_right (le_max_of_le_left (norm_nonneg I))] using hh.trans_lt hhε
  have hPair : Continuous (fun a : ℝ => (a,circleParabolicTranslation T τ hτ a U)) :=
    (continuous_id : Continuous (fun a : ℝ => a)).prodMk
      (circle_parabolic_translation_continuous T τ hτ U)
  have hComposition := (circle_parabolic_static_translation_continuous T τ).comp hPair
  have hV : Continuous V := by
    simpa only [V,circleParabolicEndpointTranslation,Function.comp_def] using! hComposition
  have hVr : ‖V 0‖ < r := by
    simpa only [V,endpoint_translation_zero] using
      hU.trans_le ((min_le_right δ (min r ε)).trans (min_le_left r ε))
  have hnorm : ∀ᶠ a : ℝ in 𝓝 0, ‖V a‖ < r :=
    hV.continuousAt.norm.eventually_lt continuousAt_const hVr
  have hparam : ∀ᶠ a : ℝ in 𝓝 0, ‖z a‖ < ε :=
    hz.continuous.continuousAt.norm.eventually_lt continuousAt_const hz0
  have hIdent : ∀ᶠ a : ℝ in 𝓝 0, V a = g (z a) := by
    filter_upwards [hnorm,hparam] with a ha hz
    exact (hbranch.2 (z a) hz).2.2 (V a) ha
      (htranslated τ hτ U (hU.trans_le (min_le_left _ _)) φ hPDE a)
  let L := endpointValueCurve T τ
  let F : ℝ → C(unitInterval,CircleL2 T) := fun a => L (g (z a))
  have hzBall : z 0 ∈ Metric.ball 0 ε := by
    simpa only [Metric.mem_ball,dist_zero_right] using hz0
  have hgn : ContDiffAt ℝ ∞ g (z 0) :=
    hbranch.1.contDiffAt (Metric.isOpen_ball.mem_nhds hzBall)
  have hL : ContDiff ℝ ∞ (L : CircleParabolicSpace T τ → C(unitInterval,CircleL2 T)) := by
    simpa only using! (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
      (E := CircleParabolicSpace T τ) (F := C(unitInterval,CircleL2 T)) L)
  have hpre := hL.contDiffAt.comp 0 (hgn.comp 0 hz.contDiffAt)
  have horder : (n : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) :=
    (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)).le
  have hF : ContDiffAt ℝ n F 0 := by
    simpa only [F,Function.comp_def] using! hpre.of_le horder
  let c : C(unitInterval,ℝ) := ⟨fun t => (t:ℝ)+1,continuous_subtype_val.add_const 1⟩
  have hc (t : unitInterval) : c t ≠ 0 := ne_of_gt (by
    change 0 < (t:ℝ)+1
    linarith [t.property.1])
  have horbit : ∀ᶠ a : ℝ in 𝓝 0, ∀ t : unitInterval,
      F a t = circleL2Translation T ((a*c t:ℝ):AddCircle T) (L U t) := by
    filter_upwards [hIdent] with a ha
    intro t
    have hcurve := circle_parabolic_endpoint_translation_curve T τ hτ a U t
    exact (congrArg (fun W : CircleParabolicSpace T τ => L W t) ha.symm).trans
      ((congrArg (circleSobolevCoordinate T 2 0) hcurve).trans
        (circle_sobolev_translation_coordinate T 2 _ _ 0))
  exact circle_continuous_sobolev_of_nonvanishing_translation T n c hc (L U) F hF horbit

end Lemniscate
