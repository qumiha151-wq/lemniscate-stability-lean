import Lemniscate.PeriodicParabolicTranslation
import Lemniscate.NormalGraphTranslation
import Lemniscate.BernoulliParabolicParameterEquation

/-! A translated actual solution satisfies the actual parameter equation.
The scalar time-L2 angular velocity is unchanged. The unit domain is proved
from a small original parabolic norm, uniformly in the translation parameter.
 -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal Topology

private theorem lp_residual_zero
    {H : Type*} [NormedAddCommGroup H]
    (v F d R : Lp H 2 (volume : Measure unitInterval))
    (h : ∀ᵐ t ∂volume, v t = F t+d t-R t) : v-F-d+R = 0 := by
  have heq : v = F+d-R := by
    apply Lp.ext
    filter_upwards [h,Lp.coeFn_sub (F+d) R,Lp.coeFn_add F d] with t ht hs ha
    exact ht.trans (hs.trans (congrArg (fun x : H => x-R t) ha)).symm
  rw [heq]
  abel

private theorem rearrange_transport {H : Type*} [AddCommGroup H] (F R d : H) :
    (F-R)+d = F+d-R := by abel

private theorem translation_radius_transport {P : ℝ → Prop} {Q : Prop}
    (h : ∃ δ > 0, P δ)
    (k : ∀ δ, 0 < δ → P δ → Q) : Q := by
  obtain ⟨δ,hδ,hP⟩ := h
  exact k δ hδ hP

variable (T : ℝ) [Fact (0 < T)]

private theorem low_small_unit_domain
    (K : BackgroundJetOver C(AddCircle T, ℂ)) :
    ∃ δ > 0, ∀ h : CircleSobolevSpace T 2, ‖h‖ < δ →
      circleNormalGraphLowCoordinates T h ∈ normalGraphLowerCoefficientDomain T K := by
  obtain ⟨hopen,hzero,_⟩ := normal_graph_lower_coefficients_smooth_over C(AddCircle T, ℂ) K 0
  have hnhds : normalGraphLowerCoefficientDomain T K ∈
      𝓝 (0 : Fin 2 → C(AddCircle T, ℂ)) := hopen.mem_nhds hzero
  have hpre : (circleNormalGraphLowCoordinates T) ⁻¹'
      normalGraphLowerCoefficientDomain T K ∈ 𝓝 (0 : CircleSobolevSpace T 2) := by
    apply (circleNormalGraphLowCoordinates T).continuous.continuousAt.preimage_mem_nhds
    simpa only [map_zero] using hnhds
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hpre
  exact ⟨δ,hδ,fun h hh => hball (by simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hh)⟩

private theorem time_domain_of_spatial_low_domains
    (τ : ℝ) (b : Fin 6 → CircleTimeCoefficient T) (U : CircleParabolicSpace T τ)
    (hdom : ∀ t : unitInterval, circleNormalGraphLowCoordinates T (circleParabolicCurve T τ U t) ∈
      normalGraphLowerCoefficientDomain T (circleTimeNormalGraphBackground T b t)) :
    (b,U) ∈ circleParabolicNormalGraphDomain T τ := by
  change IsUnit (1-b 0*circleParabolicLowCoordinates T τ U 0) ∧
    IsUnit ((1-b 0*circleParabolicLowCoordinates T τ U 0)^2+
      (circleParabolicLowCoordinates T τ U 1)^2)
  constructor
  · apply (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr
    rintro ⟨t,x⟩
    have hA : IsUnit (1-(circleTimeNormalGraphBackground T b t).k*
        circleNormalGraphLowCoordinates T (circleParabolicCurve T τ U t) 0) := (hdom t).1
    have hx := (ContinuousMap.isUnit_iff_forall_ne_zero _).mp hA x
    change 1-b 0 (t,x)*
      circleNormalGraphLowCoordinates T (circleParabolicCurve T τ U t) 0 x ≠ 0 at hx
    change 1-b 0 (t,x)*circleParabolicLowCoordinates T τ U 0 (t,x) ≠ 0
    rw [circle_parabolic_low_coordinates_apply]
    exact hx
  · apply (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr
    rintro ⟨t,x⟩
    have hH : IsUnit ((1-(circleTimeNormalGraphBackground T b t).k*
        circleNormalGraphLowCoordinates T (circleParabolicCurve T τ U t) 0)^2+
        (circleNormalGraphLowCoordinates T (circleParabolicCurve T τ U t) 1)^2) := (hdom t).2
    have hx := (ContinuousMap.isUnit_iff_forall_ne_zero _).mp hH x
    change (1-b 0 (t,x)*
      circleNormalGraphLowCoordinates T (circleParabolicCurve T τ U t) 0 x)^2+
      (circleNormalGraphLowCoordinates T (circleParabolicCurve T τ U t) 1 x)^2 ≠ 0 at hx
    change (1-b 0 (t,x)*circleParabolicLowCoordinates T τ U 0 (t,x))^2+
      (circleParabolicLowCoordinates T τ U 1 (t,x))^2 ≠ 0
    have heq := congrArg₂ (fun z w : ℂ => (1-b 0 (t,x)*z)^2+w^2)
      (circle_parabolic_low_coordinates_apply T τ U 0 t x)
      (circle_parabolic_low_coordinates_apply T τ U 1 t x)
    intro hz
    exact hx (heq.symm.trans hz)

private theorem background_slice_translation
    (q p : C(AddCircle T, ℂ)) (a : ℝ) (t : unitInterval) :
    circleTimeNormalGraphBackground T (circleBernoulliParabolicBackground T q p a) t =
      circleNormalGraphBackgroundTranslation T ((a*(t:ℝ):ℝ) : AddCircle T)
        (circleBernoulliBackground T q p) := by
  rfl

set_option maxHeartbeats 1200000 in
/-- One covariance argument applies to every actual translated solution:
the spatial shift may depend on time, while its transport velocity is
specified by the actual parabolic derivative representative. -/
theorem bernoulli_parabolic_translated_residual
    (q p : C(AddCircle T, ℂ)) :
    ∃ δ > 0, ∀ τ : ℝ, ∀ U : CircleParabolicSpace T τ, ‖U‖ < δ →
      ∀ φ : Lp ℂ 2 (volume : Measure unitInterval),
      (∀ᵐ t : unitInterval ∂volume, circleParabolicTimeDerivative T τ U t =
        circleNormalGraphFlow T (circleBernoulliBackground T q p) (15/2) (circleParabolicH4 T τ U t)-
          φ t • circleNormalGraphRotationField T (circleBernoulliBackground T q p)
            (circleParabolicCurve T τ U t)) →
      ∀ b : Fin 6 → CircleTimeCoefficient T, ∀ V : CircleParabolicSpace T τ,
      ∀ shift : unitInterval → AddCircle T, ∀ α : ℂ,
      (∀ t, circleTimeNormalGraphBackground T b t =
        circleNormalGraphBackgroundTranslation T (shift t) (circleBernoulliBackground T q p)) →
      (∀ t, circleParabolicCurve T τ V t =
        circleSobolevTranslation T 2 (shift t) (circleParabolicCurve T τ U t)) →
      (∀ᵐ t ∂volume, circleParabolicH4 T τ V t =
        circleSobolevTranslation T 4 (shift t) (circleParabolicH4 T τ U t)) →
      (∀ᵐ t ∂volume, circleParabolicTimeDerivative T τ V t =
        circleL2Translation T (shift t) (circleParabolicTimeDerivative T τ U t)+
          α • circleSobolevCoordinate T 4 1
            (circleSobolevTranslation T 4 (shift t) (circleParabolicH4 T τ U t))) →
      (b,V) ∈ circleParabolicNormalGraphDomain T τ ∧
        circleParabolicTimeDerivative T τ V-circleParabolicNormalGraphFlow T τ (15/2) (b,V)-
          α • ((circleSobolevCoordinate T 4 1).compLpL 2
            (volume : Measure unitInterval) (circleParabolicH4 T τ V))+
          circleParabolicRotationAction T τ ((b,V),φ) = 0 := by
  let K := circleBernoulliBackground T q p
  refine translation_radius_transport (low_small_unit_domain T K) ?_
  intro δ hδ hlow
  refine ⟨δ,hδ,?_⟩
  intro τ U hU φ hPDE b Ua shift α hbackground hcurve h4 hvelocity
  have hpoint (t : unitInterval) :
      circleNormalGraphLowCoordinates T (circleParabolicCurve T τ U t) ∈
        normalGraphLowerCoefficientDomain T K :=
    hlow _ (((circleParabolicCurve T τ U).norm_coe_le_norm t).trans_lt
      ((norm_fst_le U.1).trans_lt hU))
  have htranslated (t : unitInterval) :
      circleNormalGraphLowCoordinates T (circleParabolicCurve T τ Ua t) ∈
        normalGraphLowerCoefficientDomain T (circleTimeNormalGraphBackground T b t) := by
    have hs := (circle_normal_graph_translation T K (shift t) (15/2)
      0 (circleParabolicCurve T τ U t)).2.1.mp (hpoint t)
    exact (congrArg₂ (fun k u => circleNormalGraphLowCoordinates T u ∈
      normalGraphLowerCoefficientDomain T k) (hbackground t).symm (hcurve t).symm) ▸ hs
  have hdom : (b,Ua) ∈ circleParabolicNormalGraphDomain T τ :=
    time_domain_of_spatial_low_domains T τ b Ua htranslated
  have hfdom : ∀ᵐ t : unitInterval ∂volume,
      circleParabolicH4 T τ U t ∈ circleNormalGraphDomain T K := by
    filter_upwards [circle_parabolic_h2_h4_ae T τ U] with t ht
    apply (circle_normal_graph_domain_iff_low T K _).mpr
    exact Eq.mp (congrArg (fun h : CircleSobolevSpace T 2 =>
      circleNormalGraphLowCoordinates T h ∈ normalGraphLowerCoefficientDomain T K) ht) (hpoint t)
  let V := circleParabolicTimeDerivative T τ Ua
  let F := circleParabolicNormalGraphFlow T τ (15/2) (b,Ua)
  let D : CircleTimeL2 T :=
    (circleSobolevCoordinate T 4 1).compLpL 2 (volume : Measure unitInterval)
      (circleParabolicH4 T τ Ua)
  let R := circleParabolicRotationAction T τ ((b,Ua),φ)
  have hF := circle_parabolic_normal_graph_flow_ae T τ (15/2) b Ua hdom
  have hR := (circle_parabolic_rotation_ae T τ b Ua hdom).2 φ
  have hD := (circleSobolevCoordinate T 4 1).coeFn_compLpL
    (p := 2) (μ := (volume : Measure unitInterval)) (circleParabolicH4 T τ Ua)
  have hresidualAE : ∀ᵐ t ∂volume, V t = F t+(α • D) t-R t := by
    filter_upwards [h4,hvelocity,hF,hR,hD,Lp.coeFn_smul α D,hPDE,hfdom]
      with t h4 hv hFt hRt hDt hα hPt hdomt
    let s : AddCircle T := shift t
    let S := circleL2Translation T s
    have hK : circleTimeNormalGraphBackground T b t = circleNormalGraphBackgroundTranslation T s K :=
      hbackground t
    have hs := circle_normal_graph_translation T K s (15/2)
      (circleParabolicH4 T τ U t) (circleParabolicCurve T τ U t)
    have hFF : F t = S (circleNormalGraphFlow T K (15/2) (circleParabolicH4 T τ U t)) :=
      hFt.trans ((congrArg₂ (fun k f => circleNormalGraphFlow T k (15/2) f) hK h4).trans
        (hs.2.2.1 hdomt))
    have hRR : R t = φ t • S (circleNormalGraphRotationField T K (circleParabolicCurve T τ U t)) := by
      have hc := hcurve t
      exact hRt.trans (congrArg (φ t • ·)
        ((congrArg₂ (circleNormalGraphRotationField T) hK hc).trans (hs.2.2.2 (hpoint t))))
    have hDD : (α • D) t = α • circleSobolevCoordinate T 4 1
        (circleSobolevTranslation T 4 s (circleParabolicH4 T τ U t)) :=
      hα.trans (congrArg (α • ·) (hDt.trans (congrArg (circleSobolevCoordinate T 4 1) h4)))
    have hS : S (circleParabolicTimeDerivative T τ U t) =
        S (circleNormalGraphFlow T K (15/2) (circleParabolicH4 T τ U t))-
          φ t • S (circleNormalGraphRotationField T K (circleParabolicCurve T τ U t)) := by
      simpa only [map_sub,map_smul] using congrArg S hPt
    calc
      V t = S (circleParabolicTimeDerivative T τ U t)+
          α • circleSobolevCoordinate T 4 1
            (circleSobolevTranslation T 4 s (circleParabolicH4 T τ U t)) := hv
      _ = (S (circleNormalGraphFlow T K (15/2) (circleParabolicH4 T τ U t))-
          φ t • S (circleNormalGraphRotationField T K (circleParabolicCurve T τ U t)))+
          α • circleSobolevCoordinate T 4 1
            (circleSobolevTranslation T 4 s (circleParabolicH4 T τ U t)) :=
        congrArg (fun v : CircleL2 T => v+α • circleSobolevCoordinate T 4 1
          (circleSobolevTranslation T 4 s (circleParabolicH4 T τ U t))) hS
      _ = S (circleNormalGraphFlow T K (15/2) (circleParabolicH4 T τ U t))+
          α • circleSobolevCoordinate T 4 1
            (circleSobolevTranslation T 4 s (circleParabolicH4 T τ U t))-
          φ t • S (circleNormalGraphRotationField T K (circleParabolicCurve T τ U t)) :=
        rearrange_transport _ _ _
      _ = F t+(α • D) t-R t :=
        congrArg₂ (fun x y : CircleL2 T => x-y)
          (congrArg₂ (fun x y : CircleL2 T => x+y) hFF.symm hDD.symm) hRR.symm
  exact ⟨hdom,lp_residual_zero V F (α • D) R hresidualAE⟩

set_option maxHeartbeats 800000 in
/-- Translating a genuine small parabolic solution gives a solution of the
actual spatial-translation parameter equation, with its original scalar
angular velocity and original initial height. The same smallness radius
works for every real translation parameter and every nonzero duration. -/
theorem bernoulli_parabolic_translation_equation
    (q p : C(AddCircle T, ℂ)) :
    ∃ δ > 0, ∀ τ : ℝ, ∀ hτ : τ ≠ 0, ∀ U : CircleParabolicSpace T τ, ‖U‖ < δ →
      ∀ φ : Lp ℂ 2 (volume : Measure unitInterval),
      (∀ᵐ t : unitInterval ∂volume, circleParabolicTimeDerivative T τ U t =
        circleNormalGraphFlow T (circleBernoulliBackground T q p) (15/2) (circleParabolicH4 T τ U t)-
          φ t • circleNormalGraphRotationField T (circleBernoulliBackground T q p)
            (circleParabolicCurve T τ U t)) →
      ∀ a : ℝ,
        let Ua := circleParabolicTranslation T τ hτ a U
        ((a,circleParabolicInitialValue T τ U,φ),Ua) ∈
          circleBernoulliParabolicParameterDomain T τ q p ∧
        circleBernoulliParabolicParameterEquation T τ q p
          ((a,circleParabolicInitialValue T τ U,φ),Ua) = 0 := by
  refine translation_radius_transport (bernoulli_parabolic_translated_residual T q p) ?_
  intro δ hδ hresidual
  refine ⟨δ,hδ,?_⟩
  intro τ hτ U hU φ hPDE a
  let Ua := circleParabolicTranslation T τ hτ a U
  have hcomp := circle_parabolic_translation_components T τ hτ a U
  have h := hresidual τ U hU φ hPDE (circleBernoulliParabolicBackground T q p a) Ua
    (fun t => ((a*(t:ℝ):ℝ) : AddCircle T)) ((a/τ:ℝ):ℂ)
    (background_slice_translation T q p a)
    (circle_parabolic_translation_curve T τ hτ a U) hcomp.1 hcomp.2.1
  refine ⟨h.1,?_⟩
  change (circleParabolicInitialValue T τ Ua-circleParabolicInitialValue T τ U,_) = 0
  exact Prod.ext (sub_eq_zero.mpr hcomp.2.2) h.2

end Lemniscate
