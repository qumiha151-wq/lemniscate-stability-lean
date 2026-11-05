import Lemniscate.BernoulliParabolicImplicitSolution
import Lemniscate.BernoulliParabolicTranslationEquation
import Lemniscate.PeriodicSobolevTranslationRegularity
import Mathlib.Data.Finset.Lattice.Fold

/-! Spatial smoothing of the actual unmodulated equation on the given time
interval and with its given linear data inverse. One neighbourhood gives all
Sobolev orders; quantitative bounds shrink only the initial/phase data radius.
 -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff BigOperators

private theorem branch_identification
    {P X Y : Type*} [NormedAddCommGroup P] [NormedAddCommGroup X] [Zero Y]
    (F : (ℝ × P) × X → Y) (g : ℝ × P → X) (ε r : ℝ)
    (hunique : ∀ z : ℝ × P, ‖z‖ < ε → ∀ x : X,
      ‖x‖ < r → F (z,x) = 0 → x = g z)
    (V : ℝ → X) (hV : ContinuousAt V 0) (d : P)
    (hd : ‖d‖ < ε) (hV0 : ‖V 0‖ < r)
    (heq : ∀ a : ℝ, F ((a,d),V a) = 0) :
    ∀ᶠ a : ℝ in 𝓝 0, V a = g (a,d) := by
  have hv : ∀ᶠ a : ℝ in 𝓝 0, ‖V a‖ < r :=
    hV.norm.eventually_lt continuousAt_const hV0
  have hp0 : ‖((0:ℝ),d)‖ < ε := by
    simpa only [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg d)] using hd
  have hp : ∀ᶠ a : ℝ in 𝓝 0, ‖(a,d)‖ < ε :=
    ((continuous_id.prodMk continuous_const).norm.continuousAt).eventually_lt
      continuousAt_const hp0
  filter_upwards [hv,hp] with a hva hpa
  exact hunique (a,d) hpa (V a) hva (heq a)

private theorem finite_parameter_derivative_bound
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ × P → E) (ε : ℝ) (hε : 0 < ε)
    (hF : ContDiffOn ℝ ∞ F (Metric.ball 0 ε))
    (hzero : ∀ a : ℝ, (a,(0:P)) ∈ Metric.ball 0 ε → F (a,0) = 0)
    (n : ℕ) (r₀ : ℝ) (hr₀ : 0 < r₀) :
    ∃ d > 0, ∃ C > 0, ∀ q : P, ‖q‖ < d →
      (∑ j : Fin (n+1), (((r₀⁻¹)^j.val)*
        ‖iteratedDeriv j.val (fun a : ℝ => F (a,q)) 0‖)^2) ≤ C*‖q‖^2 := by
  have h0 : ((0:ℝ),(0:P)) ∈ Metric.ball 0 ε := by simpa using hε
  have hex (j : Fin (n+1)) :=
    smooth_parameter_derivative_estimate F (Metric.ball 0 ε) Metric.isOpen_ball h0 hF hzero j.val
  choose d hd C hC hbound using hex
  let d₀ := Finset.univ.inf' Finset.univ_nonempty d
  have hd₀ : 0 < d₀ := (Finset.lt_inf'_iff _).2 (fun j _ => hd j)
  let A : ℝ := ∑ j : Fin (n+1), (((r₀⁻¹)^j.val)*C j)^2
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  refine ⟨d₀,hd₀,A+1,by positivity,?_⟩
  intro q hq
  have hj (j : Fin (n+1)) :
      (((r₀⁻¹)^j.val)*‖iteratedDeriv j.val (fun a : ℝ => F (a,q)) 0‖)^2 ≤
        ((((r₀⁻¹)^j.val)*C j)^2)*‖q‖^2 := by
    have hqj : ‖q‖ < d j := hq.trans_le (Finset.inf'_le _ (Finset.mem_univ j))
    have hscale : ((r₀⁻¹)^j.val)*‖iteratedDeriv j.val (fun a : ℝ => F (a,q)) 0‖ ≤
        (((r₀⁻¹)^j.val)*C j)*‖q‖ :=
      (mul_le_mul_of_nonneg_left (hbound j q hqj)
        (pow_nonneg (inv_nonneg.mpr hr₀.le) j.val)).trans_eq (mul_assoc _ _ _).symm
    have hw : 0 ≤ (r₀⁻¹)^j.val := pow_nonneg (inv_nonneg.mpr hr₀.le) j.val
    exact ((sq_le_sq₀ (mul_nonneg hw (norm_nonneg _))
      (mul_nonneg (mul_nonneg hw (hC j).le) (norm_nonneg q))).2 hscale).trans_eq (mul_pow _ _ 2)
  calc
    _ ≤ ∑ j : Fin (n+1), ((((r₀⁻¹)^j.val)*C j)^2)*‖q‖^2 :=
      Finset.sum_le_sum (fun j _ => hj j)
    _ = A*‖q‖^2 := (Finset.sum_mul _ _ _).symm
    _ ≤ (A+1)*‖q‖^2 := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (sq_nonneg _)

private theorem smoothing_implicit_transport
    {P X : Type*} {A : ℝ → ℝ → (P → X) → Prop} {Q : Prop}
    (h : ∃ ε > 0, ∃ r > 0, ∃ g : P → X, A ε r g)
    (k : ∀ ε, 0 < ε → ∀ r, 0 < r → ∀ g : P → X, A ε r g → Q) : Q := by
  obtain ⟨ε,hε,r,hr,g,hA⟩ := h
  exact k ε hε r hr g hA

private theorem smoothing_radius_transport {A : ℝ → Prop} {Q : Prop}
    (h : ∃ δ > 0, A δ) (k : ∀ δ, 0 < δ → A δ → Q) : Q := by
  obtain ⟨δ,hδ,hA⟩ := h
  exact k δ hδ hA

private theorem smoothing_two_radius_transport {A : ℝ → ℝ → Prop} {Q : Prop}
    (h : ∃ d > 0, ∃ C > 0, A d C)
    (k : ∀ d, 0 < d → ∀ C, 0 < C → A d C → Q) : Q := by
  obtain ⟨d,hd,C,hC,hA⟩ := h
  exact k d hd C hC hA

private theorem smoothing_witness_transport {X : Type*} {A : X → Prop} {Q : Prop}
    (h : ∃ x, A x) (k : ∀ x, A x → Q) : Q := by
  obtain ⟨x,hx⟩ := h
  exact k x hx

variable (T : ℝ) [Fact (0 < T)]

private theorem smoothing_l2_translation_zero (f : CircleL2 T) :
    circleL2Translation T 0 f = f := by
  apply circle_fourier_ext T
  intro n
  rw [circle_l2_translation_fourier,fourier_eval_zero,one_mul]

set_option maxHeartbeats 800000 in
private theorem parabolic_translation_zero (τ : ℝ) (hτ : τ ≠ 0) (U : CircleParabolicSpace T τ) :
    circleParabolicTranslation T τ hτ 0 U = U := by
  let V := circleParabolicTranslation T τ hτ 0 U
  have hcomp := circle_parabolic_translation_components T τ hτ 0 U
  have hc : circleParabolicCurve T τ V = circleParabolicCurve T τ U := by
    apply ContinuousMap.ext
    intro t
    simpa only [zero_mul,AddCircle.coe_zero,circle_sobolev_translation_zero] using
      circle_parabolic_translation_curve T τ hτ 0 U t
  have hh : circleParabolicH4 T τ V = circleParabolicH4 T τ U := by
    apply Lp.ext
    exact hcomp.1.mono (fun _ h => by
      simpa only [zero_mul,AddCircle.coe_zero,circle_sobolev_translation_zero] using h)
  have hv : circleParabolicTimeDerivative T τ V = circleParabolicTimeDerivative T τ U := by
    apply Lp.ext
    exact hcomp.2.1.mono (fun _ h => by
      simpa only [zero_mul,AddCircle.coe_zero,zero_div,Complex.ofReal_zero,
        zero_smul,add_zero,smoothing_l2_translation_zero] using h)
  apply Subtype.ext
  exact Prod.ext hc (Prod.ext hh hv)

set_option synthInstance.maxHeartbeats 80000 in
private def parabolicValueCurve (τ : ℝ) :
    CircleParabolicSpace T τ →L[ℝ] C(unitInterval,CircleL2 T) :=
  (((circleSobolevCoordinate T 2 0).compLeftContinuous ℂ unitInterval).comp
    (circleParabolicCurve T τ)).restrictScalars ℝ

private theorem parabolic_value_translation (τ : ℝ) (hτ : τ ≠ 0)
    (a : ℝ) (U : CircleParabolicSpace T τ) (t : unitInterval) :
    parabolicValueCurve T τ (circleParabolicTranslation T τ hτ a U) t =
      circleL2Translation T ((a*(t:ℝ):ℝ) : AddCircle T) (parabolicValueCurve T τ U t) := by
  change circleSobolevCoordinate T 2 0
    (circleParabolicCurve T τ (circleParabolicTranslation T τ hτ a U) t) = _
  have hc := circle_parabolic_translation_curve T τ hτ a U t
  exact (congrArg (circleSobolevCoordinate T 2 0) hc).trans
    (circle_sobolev_translation_coordinate T 2 _ _ 0)

private theorem smooth_branch_translation_smoothing
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F : ℝ × P → C(unitInterval,CircleL2 T)) (ε : ℝ) (hε : 0 < ε)
    (hF : ContDiffOn ℝ ∞ F (Metric.ball 0 ε))
    (hzero : ∀ a : ℝ, (a,(0:P)) ∈ Metric.ball 0 ε → F (a,0) = 0) :
    (∀ q : P, ‖q‖ < ε → ∀ f : C(unitInterval,CircleL2 T),
      (∀ᶠ a : ℝ in 𝓝 0, ∀ t : unitInterval,
        F (a,q) t = circleL2Translation T ((a*(t:ℝ):ℝ) : AddCircle T) (f t)) →
      ∀ n : ℕ, ∀ r₀ : ℝ, ∀ hr₀ : 0 < r₀,
        ∃ v : C(Icc r₀ (1:ℝ),CircleSobolevSpace T n), ∀ t : Icc r₀ (1:ℝ),
          circleSobolevCoordinate T n 0 (v t) =
            f ⟨(t:ℝ),(hr₀.trans_le t.property.1).le,t.property.2⟩) ∧
    (∀ n : ℕ, ∀ r₀ : ℝ, ∀ hr₀ : 0 < r₀, ∃ d > 0, ∃ C > 0,
      ∀ q : P, ‖q‖ < ε → ‖q‖ < d → ∀ f : C(unitInterval,CircleL2 T),
        (∀ᶠ a : ℝ in 𝓝 0, ∀ t : unitInterval,
          F (a,q) t = circleL2Translation T ((a*(t:ℝ):ℝ) : AddCircle T) (f t)) →
        ∃ v : C(Icc r₀ (1:ℝ),CircleSobolevSpace T n), ∀ t : Icc r₀ (1:ℝ),
          circleSobolevCoordinate T n 0 (v t) =
            f ⟨(t:ℝ),(hr₀.trans_le t.property.1).le,t.property.2⟩ ∧
          ‖v t‖^2 ≤ C*‖q‖^2) := by
  have hreg (q : P) (hq : ‖q‖ < ε) (n : ℕ) :
      ContDiffAt ℝ n (fun a : ℝ => F (a,q)) 0 := by
    have hq0 : ((0:ℝ),q) ∈ Metric.ball 0 ε := by
      simpa only [Metric.mem_ball,dist_zero_right,Prod.norm_def,norm_zero,
        max_eq_right (norm_nonneg q)] using hq
    have hopenBall : IsOpen (Metric.ball (0 : ℝ × P) ε) := Metric.isOpen_ball
    have hFq := (hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
      (hopenBall.mem_nhds hq0)
    exact hFq.comp 0 (contDiff_id.prodMk contDiff_const).contDiffAt
  constructor
  · intro q hq f ht n r₀ hr₀
    obtain ⟨v,hv⟩ := circle_continuous_sobolev_of_translation T n f (fun a => F (a,q))
      (hreg q hq n) ht r₀ hr₀
    exact ⟨v,fun t => (hv t).1⟩
  · intro n r₀ hr₀
    obtain ⟨d,hd,C,hC,hbound⟩ := finite_parameter_derivative_bound F ε hε hF hzero n r₀ hr₀
    refine ⟨d,hd,C,hC,?_⟩
    intro q hq hqd f ht
    obtain ⟨v,hv⟩ := circle_continuous_sobolev_of_translation T n f (fun a => F (a,q))
      (hreg q hq n) ht r₀ hr₀
    exact ⟨v,fun t => ⟨(hv t).1,(hv t).2.trans (hbound q hqd)⟩⟩

set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 1200000 in
/-- On a single neighbourhood of the genuine parabolic solution, all
spatial Sobolev orders are continuous away from the initial endpoint.
For each order the initial/phase data radius may shrink for a uniform
quadratic norm bound; the permitted full solution norm stays unchanged. -/
theorem bernoulli_parabolic_smoothing
    (q p : C(AddCircle T, ℂ)) (hq : HasCircleDeriv T q p)
    (hp : HasCircleDeriv T p (-(q^3))) (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (τ : ℝ) (hτ : τ ≠ 0)
    (e : CircleParabolicSpace T τ ≃L[ℂ] (CircleSobolevSpace T 2 × CircleTimeL2 T))
    (heInverse : e.toContinuousLinearMap = circleParabolicLowerOrderData T τ
      (circleSobolevCoordinate T 2 0+
        circleSobolevLowerOrderOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)))) :
    ∃ η > 0,
      (∀ U : CircleParabolicSpace T τ, ‖U‖ < η →
        ∀ φ : Lp ℂ 2 (volume : Measure unitInterval),
          ‖circleParabolicInitialValue T τ U‖+‖φ‖ < η →
          (∀ᵐ t ∂volume, circleParabolicTimeDerivative T τ U t =
            circleNormalGraphFlow T (circleBernoulliBackground T q p) (15/2) (circleParabolicH4 T τ U t)-
              φ t • circleNormalGraphRotationField T (circleBernoulliBackground T q p) (circleParabolicCurve T τ U t)) →
          ∀ n : ℕ, ∀ r₀ : ℝ, ∀ hr₀ : 0 < r₀,
            ∃ v : C(Icc r₀ (1:ℝ),CircleSobolevSpace T n), ∀ t : Icc r₀ (1:ℝ),
              circleSobolevCoordinate T n 0 (v t) =
                circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ U
                  ⟨(t:ℝ),(hr₀.trans_le t.property.1).le,t.property.2⟩)) ∧
      (∀ n : ℕ, ∀ r₀ : ℝ, ∀ hr₀ : 0 < r₀, ∃ ε > 0, ε ≤ η ∧ ∃ C > 0,
        ∀ U : CircleParabolicSpace T τ, ‖U‖ < η →
          ∀ φ : Lp ℂ 2 (volume : Measure unitInterval),
            ‖circleParabolicInitialValue T τ U‖+‖φ‖ < ε →
            (∀ᵐ t ∂volume, circleParabolicTimeDerivative T τ U t =
              circleNormalGraphFlow T (circleBernoulliBackground T q p) (15/2) (circleParabolicH4 T τ U t)-
                φ t • circleNormalGraphRotationField T (circleBernoulliBackground T q p) (circleParabolicCurve T τ U t)) →
            ∃ v : C(Icc r₀ (1:ℝ),CircleSobolevSpace T n), ∀ t : Icc r₀ (1:ℝ),
              circleSobolevCoordinate T n 0 (v t) =
                circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ U
                  ⟨(t:ℝ),(hr₀.trans_le t.property.1).le,t.property.2⟩) ∧
              ‖v t‖^2 ≤ C*(‖circleParabolicInitialValue T τ U‖+‖φ‖)^2) := by
  refine smoothing_implicit_transport
    (bernoulli_parabolic_implicit_solution T q p hq hp he τ e heInverse) ?_
  intro ε hε r hr g hbranch
  have hg := hbranch.1
  have hgdata := hbranch.2.1
  have hgzero := hbranch.2.2
  refine smoothing_radius_transport (bernoulli_parabolic_translation_equation T q p) ?_
  intro δ hδ htranslated
  let η := min δ (min r ε)
  have hη : 0 < η := lt_min hδ (lt_min hr hε)
  let L := parabolicValueCurve T τ
  let F : CircleParabolicParameter T → C(unitInterval,CircleL2 T) := fun z => L (g z)
  have hL : ContDiff ℝ ∞ (L : CircleParabolicSpace T τ → C(unitInterval,CircleL2 T)) := by
    simpa only using! (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
      (E := CircleParabolicSpace T τ) (F := C(unitInterval,CircleL2 T)) L)
  have hF : ContDiffOn ℝ ∞ F (Metric.ball 0 ε) := by
    simpa only [F,Function.comp_def] using! hL.comp_contDiffOn hg
  have hzero : ∀ a : ℝ,
      (a,(0 : CircleSobolevSpace T 2 × Lp ℂ 2 (volume : Measure unitInterval))) ∈ Metric.ball 0 ε →
      F (a,0) = 0 := by
    intro a ha
    have haNorm : ‖((a,(0 : CircleSobolevSpace T 2 ×
        Lp ℂ 2 (volume : Measure unitInterval))) : CircleParabolicParameter T)‖ < ε :=
      (dist_zero_right _).symm.trans_lt ha
    have hface : ((a,0,0) : CircleParabolicParameter T) =
        (a,(0 : CircleSobolevSpace T 2 × Lp ℂ 2 (volume : Measure unitInterval))) := rfl
    have hz := hgzero a ((congrArg (fun z : CircleParabolicParameter T => ‖z‖) hface).trans_lt haNorm)
    exact (congrArg L hz).trans L.map_zero
  have hpacket := smooth_branch_translation_smoothing T F ε hε hF hzero
  have hdataNorm (U : CircleParabolicSpace T τ) (φ : Lp ℂ 2 (volume : Measure unitInterval)) :
      ‖(circleParabolicInitialValue T τ U,φ)‖ ≤ ‖circleParabolicInitialValue T τ U‖+‖φ‖ := by
    change max ‖circleParabolicInitialValue T τ U‖ ‖φ‖ ≤ _
    exact max_le (le_add_of_nonneg_right (norm_nonneg φ))
      (le_add_of_nonneg_left (norm_nonneg (circleParabolicInitialValue T τ U)))
  have horbit (U : CircleParabolicSpace T τ) (hU : ‖U‖ < η)
      (φ : Lp ℂ 2 (volume : Measure unitInterval))
      (hd : ‖circleParabolicInitialValue T τ U‖+‖φ‖ < η)
      (hPDE : ∀ᵐ t ∂volume, circleParabolicTimeDerivative T τ U t =
        circleNormalGraphFlow T (circleBernoulliBackground T q p) (15/2) (circleParabolicH4 T τ U t)-
          φ t • circleNormalGraphRotationField T (circleBernoulliBackground T q p) (circleParabolicCurve T τ U t)) :
      ∀ᶠ a : ℝ in 𝓝 0, ∀ t : unitInterval,
        F (a,(circleParabolicInitialValue T τ U,φ)) t =
          circleL2Translation T ((a*(t:ℝ):ℝ) : AddCircle T) (L U t) := by
    let d := (circleParabolicInitialValue T τ U,φ)
    let V : ℝ → CircleParabolicSpace T τ := fun a => circleParabolicTranslation T τ hτ a U
    have hIdent : ∀ᶠ a : ℝ in 𝓝 0, V a = g (a,d) :=
      branch_identification (circleBernoulliParabolicParameterEquation T τ q p) g ε r
        (fun z hz W hW hEq => (hgdata z hz).2.2 W hW hEq) V
        (circle_parabolic_translation_continuous T τ hτ U).continuousAt d
        ((hdataNorm U φ).trans_lt (hd.trans_le ((min_le_right δ (min r ε)).trans (min_le_right r ε))))
        (by simpa only [V,parabolic_translation_zero] using
          hU.trans_le ((min_le_right δ (min r ε)).trans (min_le_left r ε)))
        (fun a => (htranslated τ hτ U (hU.trans_le (min_le_left _ _)) φ hPDE a).2)
    filter_upwards [hIdent] with a ha
    intro t
    exact (congrArg (fun W : CircleParabolicSpace T τ => L W t) ha.symm).trans
      (parabolic_value_translation T τ hτ a U t)
  refine ⟨η,hη,?_,?_⟩
  · intro U hU φ hd hp n r₀ hr₀
    exact hpacket.1 (circleParabolicInitialValue T τ U,φ)
      ((hdataNorm U φ).trans_lt (hd.trans_le ((min_le_right δ (min r ε)).trans (min_le_right r ε))))
      (L U) (horbit U hU φ hd hp) n r₀ hr₀
  · intro n r₀ hr₀
    refine smoothing_two_radius_transport (hpacket.2 n r₀ hr₀) ?_
    intro d hd C hC hquant
    refine ⟨min η d,lt_min hη hd,min_le_left _ _,C,hC,?_⟩
    intro U hU φ hdata hp
    have hdataη := hdata.trans_le (min_le_left η d)
    have hqε := (hdataNorm U φ).trans_lt
      (hdataη.trans_le ((min_le_right δ (min r ε)).trans (min_le_right r ε)))
    have hqd := (hdataNorm U φ).trans_lt (hdata.trans_le (min_le_right η d))
    refine smoothing_witness_transport
      (hquant (circleParabolicInitialValue T τ U,φ) hqε hqd
        (L U) (horbit U hU φ hdataη hp)) ?_
    intro v hv
    refine ⟨v,fun t => ⟨(hv t).1,(hv t).2.trans ?_⟩⟩
    exact mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (hdataNorm U φ)) hC.le

end Lemniscate
