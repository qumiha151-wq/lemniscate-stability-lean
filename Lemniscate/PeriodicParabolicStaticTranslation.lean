import Lemniscate.PeriodicSobolevTranslation
import Lemniscate.PeriodicParabolicNormedSpace
import Lemniscate.PeriodicParabolicEstimates
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Algebra

/-! Constant spatial translations on the actual parabolic space. The
physical velocity is translated without an additional transport term.
The primitive is preserved by commutation of a bounded linear map with
the Bochner integral. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal Topology

section StaticTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private def staticCurveLift (J : E →ₗᵢ[ℂ] E) : C(unitInterval,E) →L[ℂ] C(unitInterval,E) :=
  J.toContinuousLinearMap.compLeftContinuous ℂ unitInterval

private def staticTimeLift (J : E →ₗᵢ[ℂ] E) :
    Lp E 2 (volume : Measure unitInterval) →L[ℂ] Lp E 2 (volume : Measure unitInterval) :=
  J.toContinuousLinearMap.compLpL 2 (volume : Measure unitInterval)

private theorem static_time_lift_ae (J : E →ₗᵢ[ℂ] E)
    (F : Lp E 2 (volume : Measure unitInterval)) :
    (staticTimeLift J F : unitInterval → E) =ᵐ[volume] fun t => J (F t) :=
  J.toContinuousLinearMap.coeFn_compLpL F

private theorem static_curve_lift_norm (J : E →ₗᵢ[ℂ] E) (f : C(unitInterval,E)) :
    ‖staticCurveLift J f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro t
    change ‖J (f t)‖ ≤ ‖f‖
    rw [J.norm_map]
    exact f.norm_coe_le_norm t
  · apply (f.norm_le (norm_nonneg _)).mpr
    intro t
    have ht := (staticCurveLift J f).norm_coe_le_norm t
    change ‖J (f t)‖ ≤ ‖staticCurveLift J f‖ at ht
    simpa only [J.norm_map] using ht

private theorem static_time_lift_norm (J : E →ₗᵢ[ℂ] E)
    (F : Lp E 2 (volume : Measure unitInterval)) : ‖staticTimeLift J F‖ = ‖F‖ := by
  have hpoint : ∀ᵐ t ∂(volume : Measure unitInterval),
      ‖staticTimeLift J F t‖ = ‖F t‖ := by
    filter_upwards [static_time_lift_ae J F] with t ht
    exact (congrArg norm ht).trans (J.norm_map (F t))
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (hpoint.mono fun _ h => h.le))
    (Lp.norm_le_norm_of_ae_le (hpoint.mono fun _ h => h.ge))

variable (S : ℝ → E →ₗᵢ[ℂ] E) (hS : ∀ f : E, Continuous (fun a : ℝ => S a f))
include hS

private theorem static_transport_joint_continuous :
    Continuous (fun p : ℝ × E => S p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h₁ : Tendsto (fun q : ℝ × E => ‖q.2-p.2‖) (𝓝 p) (𝓝 (0:ℝ)) := by
    simpa only [Pi.sub_apply,Function.comp_apply,sub_self,norm_zero] using
      ((continuous_snd.sub (continuous_const : Continuous
        (fun _ : ℝ × E => p.2))).norm.tendsto p)
  have h₂ : Tendsto (fun q : ℝ × E => ‖S q.1 p.2-S p.1 p.2‖) (𝓝 p) (𝓝 (0:ℝ)) := by
    simpa only [Pi.sub_apply,Function.comp_apply,sub_self,norm_zero] using
      ((((hS p.2).comp continuous_fst).sub (continuous_const : Continuous
        (fun _ : ℝ × E => S p.1 p.2))).norm.tendsto p)
  apply squeeze_zero (fun _ => norm_nonneg _) (fun q => ?_)
    (by simpa only [zero_add] using h₁.add h₂)
  calc
    ‖S q.1 q.2-S p.1 p.2‖ ≤ ‖S q.1 q.2-S q.1 p.2‖+‖S q.1 p.2-S p.1 p.2‖ :=
      by simpa only [dist_eq_norm] using
        dist_triangle (S q.1 q.2) (S q.1 p.2) (S p.1 p.2)
    _ = ‖q.2-p.2‖+‖S q.1 p.2-S p.1 p.2‖ := by rw [← map_sub,(S q.1).norm_map]

private theorem static_curve_lift_continuous (f : C(unitInterval,E)) :
    Continuous (fun a : ℝ => staticCurveLift (S a) f) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (static_transport_joint_continuous S hS).comp
    (continuous_fst.prodMk (f.continuous.comp continuous_snd))

end StaticTransport

section StaticHilbertTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : ℝ → E →ₗᵢ[ℂ] E) (hS : ∀ f : E, Continuous (fun a : ℝ => S a f))

include hS

private theorem static_time_lift_continuous
    (F : Lp E 2 (volume : Measure unitInterval)) :
    Continuous (fun a : ℝ => staticTimeLift (S a) F) := by
  apply continuous_iff_continuousAt.mpr
  intro a₀
  let e : ℝ → unitInterval → ℝ := fun a t => ‖S a (F t)-S a₀ (F t)‖^2
  have hdiff (a : ℝ) : MemLp (fun t : unitInterval => S a (F t)-S a₀ (F t)) 2 volume :=
    ((S a).toContinuousLinearMap.comp_memLp F).sub
      ((S a₀).toContinuousLinearMap.comp_memLp F)
  have hF : Integrable (fun t : unitInterval => ‖F t‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable F)).mp (Lp.memLp F)
  have hbound (a : ℝ) (t : unitInterval) : ‖e a t‖ ≤ 4*‖F t‖^2 := by
    have h : ‖S a (F t)-S a₀ (F t)‖ ≤ 2*‖F t‖ := by
      simpa only [(S a).norm_map,(S a₀).norm_map,two_mul] using
        norm_sub_le (S a (F t)) (S a₀ (F t))
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
      (norm_nonneg (F t)))).mpr h
    change ‖(‖S a (F t)-S a₀ (F t)‖ : ℝ)^2‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hpoint (t : unitInterval) : Tendsto (fun a => e a t) (𝓝 a₀) (𝓝 (0:ℝ)) := by
    simpa only [e,sub_self,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0)] using
      (((hS (F t)).tendsto a₀).sub_const (S a₀ (F t))).norm.pow 2
  have hi : Tendsto (fun a => ∫ t, e a t ∂volume) (𝓝 a₀) (𝓝 (0:ℝ)) := by
    simpa only [integral_zero] using
      (tendsto_integral_filter_of_dominated_convergence
        (f := fun _ : unitInterval => (0:ℝ)) (fun t : unitInterval => 4*‖F t‖^2)
        (Eventually.of_forall fun a =>
          ((memLp_two_iff_integrable_sq_norm (hdiff a).aestronglyMeasurable).mp
            (hdiff a)).aestronglyMeasurable)
        (Eventually.of_forall fun a => Eventually.of_forall (hbound a))
        (hF.const_mul 4) (Eventually.of_forall hpoint))
  have hnorm (a : ℝ) :
      ‖staticTimeLift (S a) F-staticTimeLift (S a₀) F‖^2 = ∫ t, e a t ∂volume := by
    rw [unit_time_l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (staticTimeLift (S a) F) (staticTimeLift (S a₀) F),
      static_time_lift_ae (S a) F,static_time_lift_ae (S a₀) F] with t ht ha ha₀
    simp only [ht,Pi.sub_apply,ha,ha₀,e]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs : Tendsto (fun a => ‖staticTimeLift (S a) F-staticTimeLift (S a₀) F‖^2)
      (𝓝 a₀) (𝓝 (0:ℝ)) := by simpa only [hnorm] using hi
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto (0:ℝ)).comp hs

end StaticHilbertTransport

variable (T : ℝ) [Fact (0 < T)] (τ : ℝ)

local instance staticTranslationSecondCountable :
    SecondCountableTopologyEither unitInterval (CircleSobolevSpace T 2) where
  out := Or.inl (inferInstance : SecondCountableTopology unitInterval)

private def staticSobolevShift (m : ℕ) (a : ℝ) :
    CircleSobolevSpace T m →ₗᵢ[ℂ] CircleSobolevSpace T m :=
  (circleSobolevTranslation T m (a:AddCircle T)).toLinearIsometry

private def staticL2Shift (a : ℝ) : CircleL2 T →ₗᵢ[ℂ] CircleL2 T :=
  circleL2Translation T (a:AddCircle T)

private theorem static_shift_coordinate (m : ℕ) (a : ℝ)
    (f : CircleSobolevSpace T m) (j : Fin (m+1)) :
    circleSobolevCoordinate T m j (staticSobolevShift T m a f) =
      staticL2Shift T a (circleSobolevCoordinate T m j f) := by
  simpa only [staticSobolevShift,staticL2Shift,circleL2Translation] using!
    (circle_sobolev_translation_coordinate T m (a:AddCircle T) f j)

private def staticParabolicAmbient (a : ℝ) (U : CircleParabolicSpace T τ) :
    CircleParabolicAmbient T :=
  (staticCurveLift (staticSobolevShift T 2 a) (circleParabolicCurve T τ U),
    staticTimeLift (staticSobolevShift T 4 a) (circleParabolicH4 T τ U),
    staticTimeLift (staticL2Shift T a) (circleParabolicTimeDerivative T τ U))

set_option maxHeartbeats 800000 in
private theorem static_parabolic_mem (a : ℝ) (U : CircleParabolicSpace T τ) :
    staticParabolicAmbient T τ a U ∈ circleParabolicSubmodule T τ := by
  let C := circleParabolicCurve T τ U
  let H := circleParabolicH4 T τ U
  let V := circleParabolicTimeDerivative T τ U
  let C' := staticCurveLift (staticSobolevShift T 2 a) C
  let H' := staticTimeLift (staticSobolevShift T 4 a) H
  let V' := staticTimeLift (staticL2Shift T a) V
  let J := (staticL2Shift T a).toContinuousLinearMap.restrictScalars ℝ
  apply (circle_parabolic_mem_iff T τ _).mpr
  constructor
  · apply Lp.ext
    have hc := (circleSobolevCoordinate T 2 0).coeFn_compLpL
      (p := 2) (μ := (volume : Measure unitInterval))
      (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℂ C')
    have hct := ContinuousMap.coeFn_toLp (p := 2)
      (volume : Measure unitInterval) (𝕜 := ℂ) C'
    have hh := (circleSobolevCoordinate T 4 0).coeFn_compLpL
      (p := 2) (μ := (volume : Measure unitInterval)) H'
    have hH := static_time_lift_ae (staticSobolevShift T 4 a) H
    filter_upwards [hc,hct,hh,hH,circle_parabolic_value_ae T τ U]
      with t hcp hctp hhp hHt hvalue
    have hC : circleSobolevCoordinate T 2 0 (C' t) =
        staticL2Shift T a (circleSobolevCoordinate T 2 0 (C t)) :=
      static_shift_coordinate T 2 a (C t) 0
    exact hcp.trans ((congrArg (circleSobolevCoordinate T 2 0) hctp).trans
      (hC.trans ((congrArg (staticL2Shift T a) hvalue).trans
        ((static_shift_coordinate T 4 a (H t) 0).symm.trans
          ((congrArg (circleSobolevCoordinate T 4 0) hHt).symm.trans hhp.symm)))))
  · intro t
    have hInt : (∫ r in Iic t, staticL2Shift T a (V r) ∂volume) =
        J (∫ r in Iic t, V r ∂volume) :=
      J.integral_comp_comm ((circle_parabolic_time_derivative_integrable T τ U).mono_measure
        Measure.restrict_le_self)
    have hVInt : (∫ r in Iic t, V' r ∂volume) =
        ∫ r in Iic t, staticL2Shift T a (V r) ∂volume :=
      integral_congr_ae (ae_restrict_of_ae (static_time_lift_ae (staticL2Shift T a) V))
    change circleSobolevCoordinate T 2 0 (C' t)-circleSobolevCoordinate T 2 0 (C' 0) =
      τ • (∫ r in Iic t, V' r ∂volume)
    calc
      circleSobolevCoordinate T 2 0 (C' t)-circleSobolevCoordinate T 2 0 (C' 0) =
          J (circleSobolevCoordinate T 2 0 (C t)-circleSobolevCoordinate T 2 0 (C 0)) := by
        exact (congrArg₂ (fun x y : CircleL2 T => x-y)
          (static_shift_coordinate T 2 a (C t) 0)
          (static_shift_coordinate T 2 a (C 0) 0)).trans (J.map_sub _ _).symm
      _ = J (τ • (∫ r in Iic t, V r ∂volume)) :=
        congrArg J (circle_parabolic_integral_identity T τ U t)
      _ = τ • J (∫ r in Iic t, V r ∂volume) := J.map_smul τ _
      _ = τ • (∫ r in Iic t, V' r ∂volume) :=
        congrArg (fun z : CircleL2 T => τ • z) (hVInt.trans hInt).symm

/-- Constant spatial translation of the actual continuous curve, H4 jet
and physical velocity, with the same time primitive. -/
def circleParabolicStaticTranslation (a : ℝ) (U : CircleParabolicSpace T τ) :
    CircleParabolicSpace T τ :=
  ⟨staticParabolicAmbient T τ a U,static_parabolic_mem T τ a U⟩

@[simp] theorem circle_parabolic_static_translation_curve (a : ℝ)
    (U : CircleParabolicSpace T τ) (t : unitInterval) :
    circleParabolicCurve T τ (circleParabolicStaticTranslation T τ a U) t =
      circleSobolevTranslation T 2 (a:AddCircle T) (circleParabolicCurve T τ U t) := rfl

/-- Actual translated representatives and initial datum. -/
theorem circle_parabolic_static_translation_components (a : ℝ) (U : CircleParabolicSpace T τ) :
    ((circleParabolicH4 T τ (circleParabolicStaticTranslation T τ a U) :
        unitInterval → CircleSobolevSpace T 4) =ᵐ[volume]
      fun t => circleSobolevTranslation T 4 (a:AddCircle T) (circleParabolicH4 T τ U t)) ∧
    ((circleParabolicTimeDerivative T τ (circleParabolicStaticTranslation T τ a U) :
        unitInterval → CircleL2 T) =ᵐ[volume]
      fun t => circleL2Translation T (a:AddCircle T) (circleParabolicTimeDerivative T τ U t)) ∧
    circleParabolicInitialValue T τ (circleParabolicStaticTranslation T τ a U) =
      circleSobolevTranslation T 2 (a:AddCircle T) (circleParabolicInitialValue T τ U) := by
  exact ⟨static_time_lift_ae (staticSobolevShift T 4 a) (circleParabolicH4 T τ U),
    static_time_lift_ae (staticL2Shift T a) (circleParabolicTimeDerivative T τ U),rfl⟩

/-- Constant spatial translation preserves the full parabolic norm. -/
theorem circle_parabolic_static_translation_norm (a : ℝ) (U : CircleParabolicSpace T τ) :
    ‖circleParabolicStaticTranslation T τ a U‖ = ‖U‖ := by
  change max ‖staticCurveLift (staticSobolevShift T 2 a) U.1.1‖
    (max ‖staticTimeLift (staticSobolevShift T 4 a) U.1.2.1‖
      ‖staticTimeLift (staticL2Shift T a) U.1.2.2‖) =
    max ‖U.1.1‖ (max ‖U.1.2.1‖ ‖U.1.2.2‖)
  exact congrArg₂ (fun x y : ℝ => max x y)
    (static_curve_lift_norm (staticSobolevShift T 2 a) U.1.1)
    (congrArg₂ (fun x y : ℝ => max x y)
      (static_time_lift_norm (staticSobolevShift T 4 a) U.1.2.1)
      (static_time_lift_norm (staticL2Shift T a) U.1.2.2))

private theorem static_parabolic_translation_strong_continuous (U : CircleParabolicSpace T τ) :
    Continuous (fun a : ℝ => circleParabolicStaticTranslation T τ a U) := by
  have hC : Continuous (fun a : ℝ =>
      staticCurveLift (staticSobolevShift T 2 a) (circleParabolicCurve T τ U)) :=
    static_curve_lift_continuous (staticSobolevShift T 2)
      (circle_sobolev_translation_continuous T 2) (circleParabolicCurve T τ U)
  have hH : Continuous (fun a : ℝ =>
      staticTimeLift (staticSobolevShift T 4 a) (circleParabolicH4 T τ U)) :=
    static_time_lift_continuous (staticSobolevShift T 4)
      (circle_sobolev_translation_continuous T 4) (circleParabolicH4 T τ U)
  have hV : Continuous (fun a : ℝ =>
      staticTimeLift (staticL2Shift T a) (circleParabolicTimeDerivative T τ U)) :=
    static_time_lift_continuous (staticL2Shift T)
      (fun f => (circle_l2_translation_continuous T f).comp (AddCircle.continuous_mk' T))
      (circleParabolicTimeDerivative T τ U)
  apply continuous_iff_continuousAt.mpr
  intro a
  apply tendsto_subtype_rng.mpr
  exact (hC.prodMk (hH.prodMk hV)).continuousAt

private def staticParabolicIsometry (a : ℝ) :
    CircleParabolicSpace T τ →ₗᵢ[ℂ] CircleParabolicSpace T τ where
  toFun := circleParabolicStaticTranslation T τ a
  map_add' U V := by
    apply Subtype.ext
    apply Prod.ext
    · exact (congrArg (staticCurveLift (staticSobolevShift T 2 a))
        ((circleParabolicCurve T τ).map_add U V)).trans
          ((staticCurveLift (staticSobolevShift T 2 a)).map_add _ _)
    · apply Prod.ext
      · exact (congrArg (staticTimeLift (staticSobolevShift T 4 a))
          ((circleParabolicH4 T τ).map_add U V)).trans
            ((staticTimeLift (staticSobolevShift T 4 a)).map_add _ _)
      · exact (congrArg (staticTimeLift (staticL2Shift T a))
          ((circleParabolicTimeDerivative T τ).map_add U V)).trans
            ((staticTimeLift (staticL2Shift T a)).map_add _ _)
  map_smul' c U := by
    apply Subtype.ext
    apply Prod.ext
    · exact (congrArg (staticCurveLift (staticSobolevShift T 2 a))
        ((circleParabolicCurve T τ).map_smul c U)).trans
          ((staticCurveLift (staticSobolevShift T 2 a)).map_smul c _)
    · apply Prod.ext
      · exact (congrArg (staticTimeLift (staticSobolevShift T 4 a))
          ((circleParabolicH4 T τ).map_smul c U)).trans
            ((staticTimeLift (staticSobolevShift T 4 a)).map_smul c _)
      · exact (congrArg (staticTimeLift (staticL2Shift T a))
          ((circleParabolicTimeDerivative T τ).map_smul c U)).trans
            ((staticTimeLift (staticL2Shift T a)).map_smul c _)
  norm_map' := circle_parabolic_static_translation_norm T τ a

/-- Spatial translation is jointly continuous in its real parameter and
the actual full parabolic solution, including its physical velocity. -/
theorem circle_parabolic_static_translation_continuous :
    Continuous (fun z : ℝ × CircleParabolicSpace T τ =>
      circleParabolicStaticTranslation T τ z.1 z.2) :=
  static_transport_joint_continuous (staticParabolicIsometry T τ)
    (static_parabolic_translation_strong_continuous T τ)

end Lemniscate
