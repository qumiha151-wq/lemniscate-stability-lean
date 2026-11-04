import Lemniscate.PeriodicSobolevTranslation
import Lemniscate.PeriodicParabolicNormedSpace
import Lemniscate.PeriodicParabolicEstimates
import Lemniscate.PeriodicFiniteParabolicSolution
import Lemniscate.ComplexPhasePrimitive
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Time-dependent spatial translations. The time variable is the unit
interval; physical velocity therefore acquires (a/tau)*D_x u. D_x is the
scaled circle-coordinate derivative and carries no sqrt(2) factor.

The primitive constraint is established separately from the continuous
and L2 component constructions below. No transformed
primitive identity is assumed.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal Topology

section StrongTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S : ℝ → E →ₗᵢ[ℂ] E) (hS : ∀ f : E, Continuous (fun r : ℝ => S r f))
include hS

private theorem isometry_transport_joint_continuous :
    Continuous (fun p : ℝ × E => S p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hc₁ : Continuous (fun q : ℝ × E => ‖q.2-p.2‖) :=
    (show Continuous (fun q : ℝ × E => q.2-p.2) from
      continuous_snd.sub continuous_const).norm
  have h₁ : Tendsto (fun q : ℝ × E => ‖q.2-p.2‖) (𝓝 p) (𝓝 (0:ℝ)) := by
    simpa only [sub_self,norm_zero] using hc₁.tendsto p
  have hc₂ : Continuous (fun q : ℝ × E => ‖S q.1 p.2-S p.1 p.2‖) :=
    (show Continuous (fun q : ℝ × E => S q.1 p.2-S p.1 p.2) from
      ((hS p.2).comp continuous_fst).sub continuous_const).norm
  have h₂ : Tendsto (fun q : ℝ × E => ‖S q.1 p.2-S p.1 p.2‖) (𝓝 p) (𝓝 (0:ℝ)) := by
    simpa only [sub_self,norm_zero] using hc₂.tendsto p
  apply squeeze_zero (fun _ => norm_nonneg _) (fun q => ?_)
    (by simpa only [zero_add] using h₁.add h₂)
  calc
    ‖S q.1 q.2-S p.1 p.2‖ ≤ ‖S q.1 q.2-S q.1 p.2‖+‖S q.1 p.2-S p.1 p.2‖ :=
      by simpa only [dist_eq_norm] using
        dist_triangle (S q.1 q.2) (S q.1 p.2) (S p.1 p.2)
    _ = ‖q.2-p.2‖+‖S q.1 p.2-S p.1 p.2‖ := by rw [← map_sub,(S q.1).norm_map]

private def continuousTimeTransport (a : ℝ) (f : C(unitInterval,E)) : C(unitInterval,E) :=
  ⟨fun t => S (a*(t:ℝ)) (f t),
    (isometry_transport_joint_continuous S hS).comp
      ((continuous_const.mul continuous_subtype_val).prodMk f.continuous)⟩

private theorem continuous_time_transport_continuous (f : C(unitInterval,E)) :
    Continuous (fun a : ℝ => continuousTimeTransport S hS a f) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (isometry_transport_joint_continuous S hS).comp
    ((continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).prodMk
      (f.continuous.comp continuous_snd))

private theorem time_transport_memLp (a : ℝ)
    (F : Lp E 2 (volume : Measure unitInterval)) :
    MemLp (fun t : unitInterval => S (a*(t:ℝ)) (F t)) 2 volume := by
  have hm : AEStronglyMeasurable (fun t : unitInterval => (a*(t:ℝ),F t)) volume :=
    (continuous_const.mul continuous_subtype_val).aestronglyMeasurable.prodMk
      (Lp.aestronglyMeasurable F)
  exact (Lp.memLp F).congr_norm
    ((isometry_transport_joint_continuous S hS).comp_aestronglyMeasurable hm)
    (Eventually.of_forall fun t => ((S (a*(t:ℝ))).norm_map (F t)).symm)

private def lpTimeTransport (a : ℝ) (F : Lp E 2 (volume : Measure unitInterval)) :
    Lp E 2 (volume : Measure unitInterval) :=
  (time_transport_memLp S hS a F).toLp (fun t : unitInterval => S (a*(t:ℝ)) (F t))

private theorem lp_time_transport_ae (a : ℝ)
    (F : Lp E 2 (volume : Measure unitInterval)) :
    (lpTimeTransport S hS a F : unitInterval → E) =ᵐ[volume]
      fun t => S (a*(t:ℝ)) (F t) :=
  MemLp.coeFn_toLp (time_transport_memLp S hS a F)

private theorem lp_time_transport_norm (a : ℝ)
    (F : Lp E 2 (volume : Measure unitInterval)) :
    ‖lpTimeTransport S hS a F‖ ≤ ‖F‖ := by
  have h : ‖lpTimeTransport S hS a F‖ ≤ (1:ℝ)*‖F‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [lp_time_transport_ae S hS a F] with t ht
    rw [ht,(S (a*(t:ℝ))).norm_map,one_mul]
  simpa only [one_mul] using h

end StrongTransport

section HilbertTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : ℝ → E →ₗᵢ[ℂ] E) (hS : ∀ f : E, Continuous (fun r : ℝ => S r f))

private theorem time_hilbert_norm_sq (F : Lp E 2 (volume : Measure unitInterval)) :
    ‖F‖^2 = ∫ t : unitInterval, ‖F t‖^2 ∂volume := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) F F)]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => (norm_sq_eq_re_inner (𝕜 := ℂ) (F t)).symm

set_option maxHeartbeats 600000 in
private theorem lp_time_transport_continuous
    (F : Lp E 2 (volume : Measure unitInterval)) :
    Continuous (fun a : ℝ => lpTimeTransport S hS a F) := by
  apply continuous_iff_continuousAt.mpr
  intro a₀
  let e : ℝ → unitInterval → ℝ :=
    fun a t => ‖S (a*(t:ℝ)) (F t)-S (a₀*(t:ℝ)) (F t)‖^2
  have hdiff (a : ℝ) : MemLp (fun t : unitInterval =>
      S (a*(t:ℝ)) (F t)-S (a₀*(t:ℝ)) (F t)) 2 volume :=
    (time_transport_memLp S hS a F).sub (time_transport_memLp S hS a₀ F)
  have hF : Integrable (fun t : unitInterval => ‖F t‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable F)).mp (Lp.memLp F)
  have hbound (a : ℝ) (t : unitInterval) : ‖e a t‖ ≤ 4*‖F t‖^2 := by
    have h : ‖S (a*(t:ℝ)) (F t)-S (a₀*(t:ℝ)) (F t)‖ ≤ 2*‖F t‖ := by
      simpa only [(S (a*(t:ℝ))).norm_map,(S (a₀*(t:ℝ))).norm_map,two_mul] using
        norm_sub_le (S (a*(t:ℝ)) (F t)) (S (a₀*(t:ℝ)) (F t))
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
      (norm_nonneg (F t)))).mpr h
    change ‖(‖S (a*(t:ℝ)) (F t)-S (a₀*(t:ℝ)) (F t)‖ : ℝ)^2‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hpoint (t : unitInterval) : Tendsto (fun a => e a t) (𝓝 a₀) (𝓝 (0:ℝ)) := by
    have ht : Tendsto (fun a : ℝ => S (a*(t:ℝ)) (F t))
        (𝓝 a₀) (𝓝 (S (a₀*(t:ℝ)) (F t))) :=
      ((hS (F t)).comp (continuous_id.mul_const (t:ℝ))).tendsto a₀
    simpa only [e,sub_self,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0)] using
      (ht.sub_const (S (a₀*(t:ℝ)) (F t))).norm.pow 2
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
      ‖lpTimeTransport S hS a F-lpTimeTransport S hS a₀ F‖^2 = ∫ t, e a t ∂volume := by
    rw [time_hilbert_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (lpTimeTransport S hS a F) (lpTimeTransport S hS a₀ F),
      lp_time_transport_ae S hS a F,lp_time_transport_ae S hS a₀ F] with t ht ha ha₀
    simp only [ht,Pi.sub_apply,ha,ha₀,e]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs : Tendsto
      (fun a => ‖lpTimeTransport S hS a F-lpTimeTransport S hS a₀ F‖^2)
      (𝓝 a₀) (𝓝 (0:ℝ)) := by simpa only [hnorm] using hi
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto (0:ℝ)).comp hs

end HilbertTransport


section UnitTimeExtension
variable {E : Type*} [NormedAddCommGroup E]

private def unitTimeZeroExtend (f : unitInterval → E) : ℝ → E :=
  fun x => if hx : x ∈ Icc (0:ℝ) 1 then f ⟨x,hx⟩ else 0

private theorem unit_time_zero_extend_apply (f : unitInterval → E) (t : unitInterval) :
    unitTimeZeroExtend f (t:ℝ) = f t := by
  simp only [unitTimeZeroExtend,dif_pos t.property]

private theorem unit_time_zero_extend_integrable (f : unitInterval → E)
    (hf : Integrable f (volume : Measure unitInterval)) :
    Integrable (unitTimeZeroExtend f) (volume : Measure ℝ) := by
  have he : (fun t : unitInterval => unitTimeZeroExtend f (t:ℝ)) = f :=
    funext (unit_time_zero_extend_apply f)
  have hi : IntegrableOn (unitTimeZeroExtend f) (Icc (0:ℝ) 1) volume := by
    apply (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mpr
    simpa only [Function.comp_def,he] using! hf
  exact hi.integrable_of_forall_notMem_eq_zero fun x hx => by
    simp only [unitTimeZeroExtend,dif_neg hx]

variable [NormedSpace ℝ E]

private theorem unit_time_integral_Iic (f : unitInterval → E) (t : unitInterval) :
    (∫ r in Iic t, f r ∂volume) =
      ∫ x in (0:ℝ)..(t:ℝ), unitTimeZeroExtend f x := by
  rw [← unit_interval_setIntegral (unitTimeZeroExtend f) t]
  apply integral_congr_ae
  exact Eventually.of_forall fun r => (unit_time_zero_extend_apply f r).symm

end UnitTimeExtension

variable (T : ℝ) [Fact (0 < T)] (τ : ℝ)

private def realSobolevShift (m : ℕ) (a : ℝ) :
    CircleSobolevSpace T m →ₗᵢ[ℂ] CircleSobolevSpace T m :=
  (circleSobolevTranslation T m (a : AddCircle T)).toLinearIsometry

private theorem real_sobolev_shift_continuous (m : ℕ) (f : CircleSobolevSpace T m) :
    Continuous (fun a : ℝ => realSobolevShift T m a f) :=
  circle_sobolev_translation_continuous T m f

private def realCircleL2Shift (a : ℝ) : CircleL2 T →ₗᵢ[ℂ] CircleL2 T :=
  circleL2Translation T (a : AddCircle T)

private theorem real_circle_l2_shift_continuous (f : CircleL2 T) :
    Continuous (fun a : ℝ => realCircleL2Shift T a f) :=
  (circle_l2_translation_continuous T f).comp (AddCircle.continuous_mk' T)

private theorem real_sobolev_shift_coordinate (m : ℕ) (a : ℝ)
    (f : CircleSobolevSpace T m) (j : Fin (m+1)) :
    circleSobolevCoordinate T m j (realSobolevShift T m a f) =
      realCircleL2Shift T a (circleSobolevCoordinate T m j f) := by
  simpa only [realSobolevShift,realCircleL2Shift,circleL2Translation] using!
    (circle_sobolev_translation_coordinate T m (a : AddCircle T) f j)

private def translatedParabolicCurve (a : ℝ) (U : CircleParabolicSpace T τ) :
    C(unitInterval,CircleSobolevSpace T 2) :=
  continuousTimeTransport (realSobolevShift T 2) (real_sobolev_shift_continuous T 2)
    a (circleParabolicCurve T τ U)

private def translatedParabolicH4 (a : ℝ) (U : CircleParabolicSpace T τ) : CircleTimeH4 T :=
  lpTimeTransport (realSobolevShift T 4) (real_sobolev_shift_continuous T 4)
    a (circleParabolicH4 T τ U)

private def translatedParabolicVelocity (a : ℝ) (U : CircleParabolicSpace T τ) : CircleTimeL2 T :=
  lpTimeTransport (realCircleL2Shift T) (real_circle_l2_shift_continuous T)
      a (circleParabolicTimeDerivative T τ U)+
    ((a/τ:ℝ):ℂ) • ((circleSobolevCoordinate T 4 1).compLpL 2
      (volume : Measure unitInterval) (translatedParabolicH4 T τ a U))

private def translatedParabolicAmbient (a : ℝ) (U : CircleParabolicSpace T τ) :
    CircleParabolicAmbient T :=
  (translatedParabolicCurve T τ a U,
    translatedParabolicH4 T τ a U,translatedParabolicVelocity T τ a U)

private theorem translated_parabolic_components_continuous (U : CircleParabolicSpace T τ) :
    Continuous (fun a : ℝ => translatedParabolicAmbient T τ a U) := by
  have hcurve : Continuous (fun a : ℝ => translatedParabolicCurve T τ a U) :=
    continuous_time_transport_continuous (realSobolevShift T 2)
      (real_sobolev_shift_continuous T 2) (circleParabolicCurve T τ U)
  have hH4 : Continuous (fun a : ℝ => translatedParabolicH4 T τ a U) :=
    lp_time_transport_continuous (realSobolevShift T 4)
      (real_sobolev_shift_continuous T 4) (circleParabolicH4 T τ U)
  have hv : Continuous (fun a : ℝ => lpTimeTransport (realCircleL2Shift T)
      (real_circle_l2_shift_continuous T) a (circleParabolicTimeDerivative T τ U)) :=
    lp_time_transport_continuous (realCircleL2Shift T)
      (real_circle_l2_shift_continuous T) (circleParabolicTimeDerivative T τ U)
  have hcoef : Continuous (fun a : ℝ => ((a/τ:ℝ):ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_id.div_const τ)
  have hD := ((circleSobolevCoordinate T 4 1).compLpL 2
    (volume : Measure unitInterval)).continuous.comp hH4
  exact hcurve.prodMk (hH4.prodMk (hv.add (hcoef.smul hD)))

private theorem translated_parabolic_value_ae (a : ℝ) (U : CircleParabolicSpace T τ) :
    ∀ᵐ t : unitInterval ∂volume,
      circleSobolevCoordinate T 2 0 (translatedParabolicCurve T τ a U t) =
        circleSobolevCoordinate T 4 0 (translatedParabolicH4 T τ a U t) := by
  filter_upwards [circle_parabolic_value_ae T τ U,
    lp_time_transport_ae (realSobolevShift T 4) (real_sobolev_shift_continuous T 4)
      a (circleParabolicH4 T τ U)] with t hvalue hH4
  have hleft : circleSobolevCoordinate T 2 0 (translatedParabolicCurve T τ a U t) =
      realCircleL2Shift T (a*(t:ℝ))
        (circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ U t)) :=
    real_sobolev_shift_coordinate T 2 (a*(t:ℝ)) (circleParabolicCurve T τ U t) 0
  have hright : circleSobolevCoordinate T 4 0 (translatedParabolicH4 T τ a U t) =
      realCircleL2Shift T (a*(t:ℝ))
        (circleSobolevCoordinate T 4 0 (circleParabolicH4 T τ U t)) :=
    (congrArg (fun f : CircleSobolevSpace T 4 => circleSobolevCoordinate T 4 0 f) hH4).trans
      (real_sobolev_shift_coordinate T 4 (a*(t:ℝ)) (circleParabolicH4 T τ U t) 0)
  exact hleft.trans ((congrArg (fun f : CircleL2 T => realCircleL2Shift T (a*(t:ℝ)) f)
    hvalue).trans hright.symm)


private theorem scalarize_unit_primitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] ℂ) (u v : unitInterval → E) (hv : Integrable v volume)
    (τ : ℝ) (hprimitive : ∀ t : unitInterval, u t-u 0=τ • ∫ r in Iic t, v r ∂volume)
    (t : unitInterval) :
    L (u t)-L (u 0) =
      ∫ x in (0:ℝ)..(t:ℝ), τ • unitTimeZeroExtend (fun r => L (v r)) x := by
  have h := congrArg L (hprimitive t)
  rw [map_sub,map_smul] at h
  rw [← L.integral_comp_comm hv.integrableOn,unit_time_integral_Iic] at h
  rw [intervalIntegral.integral_smul]
  exact h

private theorem parabolic_scalar_primitive (U : CircleParabolicSpace T τ)
    (L : CircleL2 T →L[ℂ] ℂ) (t : unitInterval) :
    L (circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ U t))-
        L (circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ U 0)) =
      ∫ x in (0:ℝ)..(t:ℝ),
        τ • unitTimeZeroExtend (fun r => L (circleParabolicTimeDerivative T τ U r)) x := by
  simpa only using! (scalarize_unit_primitive
    (L.restrictScalars ℝ)
    (fun r => circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ U r))
    (circleParabolicTimeDerivative T τ U)
    (circle_parabolic_time_derivative_integrable T τ U) τ
    (circle_parabolic_integral_identity T τ U) t)

private theorem parabolic_scalar_velocity_zero_extend_integrable (U : CircleParabolicSpace T τ)
    (L : CircleL2 T →L[ℂ] ℂ) :
    Integrable (fun x : ℝ =>
      τ • unitTimeZeroExtend (fun r => L (circleParabolicTimeDerivative T τ U r)) x) volume :=
  (unit_time_zero_extend_integrable _
    (L.integrable_comp (circle_parabolic_time_derivative_integrable T τ U))).smul τ


private theorem translation_fourier_phase (n : ℤ) (a t : ℝ) :
    fourier n ((a*t:ℝ) : AddCircle T) =
      Complex.exp ((circleFrequencyFactor T n*(a:ℂ))*(t:ℂ)) := by
  rw [fourier_coe_apply]
  congr 1
  simp only [circleFrequencyFactor,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_intCast,Complex.ofReal_ofNat]
  ring

/-- Zero spatial translation fixes the complete Sobolev derivative jet. -/
theorem circle_sobolev_translation_zero (m : ℕ) (f : CircleSobolevSpace T m) :
    circleSobolevTranslation T m (0 : AddCircle T) f = f := by
  apply (circleSobolevTranslation T m (0 : AddCircle T)).injective
  simpa only [zero_add] using circle_sobolev_translation_add T m 0 0 f

private def parabolicFourierFunctional (n : ℤ) : CircleL2 T →L[ℂ] ℂ :=
  innerSL ℂ (fourierBasis (T := T) n)

private theorem parabolic_fourier_functional_apply (n : ℤ) (f : CircleL2 T) :
    parabolicFourierFunctional T n f = fourierCoeff f n := by
  change inner ℂ (fourierBasis (T := T) n) f = fourierCoeff f n
  rw [← HilbertBasis.repr_apply_apply,fourierBasis_repr]

private theorem parabolic_fourier_primitive (U : CircleParabolicSpace T τ) (n : ℤ)
    (t : unitInterval) :
    let y₀ := parabolicFourierFunctional T n
      (circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ U 0))
    let f := fun x : ℝ => τ • unitTimeZeroExtend
      (fun r => parabolicFourierFunctional T n (circleParabolicTimeDerivative T τ U r)) x
    y₀+∫ x in (0:ℝ)..(t:ℝ), f x =
      parabolicFourierFunctional T n
        (circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ U t)) := by
  dsimp only
  exact (add_comm _ _).trans
    (sub_eq_iff_eq_add.mp (parabolic_scalar_primitive T τ U (parabolicFourierFunctional T n) t)).symm


private theorem translated_parabolic_velocity_ae (a : ℝ) (U : CircleParabolicSpace T τ) :
    (translatedParabolicVelocity T τ a U : unitInterval → CircleL2 T) =ᵐ[volume]
      fun t => circleL2Translation T ((a*(t:ℝ):ℝ) : AddCircle T)
          (circleParabolicTimeDerivative T τ U t)+
        ((a/τ:ℝ):ℂ) • circleSobolevCoordinate T 4 1
          (circleSobolevTranslation T 4 ((a*(t:ℝ):ℝ) : AddCircle T)
            (circleParabolicH4 T τ U t)) := by
  let W := lpTimeTransport (realCircleL2Shift T) (real_circle_l2_shift_continuous T)
    a (circleParabolicTimeDerivative T τ U)
  let H := translatedParabolicH4 T τ a U
  let D := (circleSobolevCoordinate T 4 1).compLpL 2 (volume : Measure unitInterval) H
  let c : ℂ := ((a/τ:ℝ):ℂ)
  filter_upwards [Lp.coeFn_add W (c • D),Lp.coeFn_smul c D,
    lp_time_transport_ae (realCircleL2Shift T) (real_circle_l2_shift_continuous T)
      a (circleParabolicTimeDerivative T τ U),
    (circleSobolevCoordinate T 4 1).coeFn_compLpL (p := 2)
      (μ := (volume : Measure unitInterval)) H,
    lp_time_transport_ae (realSobolevShift T 4) (real_sobolev_shift_continuous T 4)
      a (circleParabolicH4 T τ U)] with t hadd hsmul hW hD hH
  have h₁ : (W+c • D) t = W t+(c • D) t := hadd
  have h₂ : W t+(c • D) t = W t+c • D t :=
    congrArg (fun q : CircleL2 T => W t+q) hsmul
  have hD' : D t = circleSobolevCoordinate T 4 1
      (realSobolevShift T 4 (a*(t:ℝ)) (circleParabolicH4 T τ U t)) :=
    hD.trans (congrArg (fun f : CircleSobolevSpace T 4 => circleSobolevCoordinate T 4 1 f) hH)
  have h₃ := congrArg₂ (fun p q : CircleL2 T => p+c • q) hW hD'
  exact h₁.trans (h₂.trans h₃)

private theorem parabolic_membership_of_representatives
    (u : C(unitInterval,CircleSobolevSpace T 2)) (w : CircleTimeH4 T) (v : CircleTimeL2 T)
    (hvalue : ∀ᵐ t : unitInterval ∂volume,
      circleSobolevCoordinate T 2 0 (u t) = circleSobolevCoordinate T 4 0 (w t))
    (hprimitive : ∀ t : unitInterval,
      circleSobolevCoordinate T 2 0 (u t)-circleSobolevCoordinate T 2 0 (u 0) =
        τ • ∫ r in Iic t, v r ∂volume) :
    (u,w,v) ∈ circleParabolicSubmodule T τ := by
  apply (circle_parabolic_mem_iff T τ (u,w,v)).mpr
  refine ⟨?_,hprimitive⟩
  apply Lp.ext
  filter_upwards [hvalue,
    (circleSobolevCoordinate T 2 0).coeFn_compLpL (p := 2)
      (μ := (volume : Measure unitInterval))
      (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℂ u),
    ContinuousMap.coeFn_toLp (p := 2) (volume : Measure unitInterval) (𝕜 := ℂ) u,
    (circleSobolevCoordinate T 4 0).coeFn_compLpL (p := 2)
      (μ := (volume : Measure unitInterval)) w] with t ht hu hU hw
  rw [hu,hU,hw]
  exact ht


private theorem parabolic_fourier_functional_shift (n : ℤ) (a : AddCircle T)
    (f : CircleL2 T) :
    parabolicFourierFunctional T n (circleL2Translation T a f) =
      fourier n a*parabolicFourierFunctional T n f := by
  simp only [parabolic_fourier_functional_apply,circle_l2_translation_fourier]

private theorem parabolic_fourier_functional_deriv (n : ℤ) (f : CircleSobolevSpace T 4) :
    parabolicFourierFunctional T n (circleSobolevCoordinate T 4 1 f) =
      circleFrequencyFactor T n*parabolicFourierFunctional T n
        (circleSobolevCoordinate T 4 0 f) := by
  have hweak : HasWeakCircleDeriv T (circleSobolevCoordinate T 4 0 f)
      (circleSobolevCoordinate T 4 1 f) := by
    simpa only using! (circle_sobolev_weak_deriv T 4 f (0 : Fin 4))
  simpa only [parabolic_fourier_functional_apply] using!
    (fourier_of_weak_circle_deriv T _ _ hweak n)

private theorem parabolic_fourier_shift_coordinate (m : ℕ) (n : ℤ) (a : ℝ)
    (f : CircleSobolevSpace T m) (j : Fin (m+1)) :
    parabolicFourierFunctional T n (circleSobolevCoordinate T m j (realSobolevShift T m a f)) =
      fourier n (a : AddCircle T)*parabolicFourierFunctional T n
        (circleSobolevCoordinate T m j f) :=
  (congrArg (parabolicFourierFunctional T n)
    (real_sobolev_shift_coordinate T m a f j)).trans
      (parabolic_fourier_functional_shift T n (a : AddCircle T) _)

private theorem complex_linear_pair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : E →L[ℂ] ℂ) (x y : E) (c : ℂ) :
    L (x+c • y)=L x+c*L y := by rw [map_add,map_smul,smul_eq_mul]

private theorem physical_phase_integrand (τ a : ℝ) (hτ : τ ≠ 0)
    (ν φ y v : ℂ) :
    φ*(τ • v)+(ν*(a:ℂ))*φ*y =
      τ • (φ*v+((a/τ:ℝ):ℂ) • (ν*φ*y)) := by
  have hτC : (τ:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ
  simp only [Complex.real_smul,smul_eq_mul,Complex.ofReal_div]
  field_simp [hτC]
  <;> ring

set_option maxHeartbeats 600000 in
private theorem translated_parabolic_primitive (hτ : τ ≠ 0) (a : ℝ)
    (U : CircleParabolicSpace T τ) (t : unitInterval) :
    circleSobolevCoordinate T 2 0 (translatedParabolicCurve T τ a U t)-
        circleSobolevCoordinate T 2 0 (translatedParabolicCurve T τ a U 0) =
      τ • (∫ r in Iic t, translatedParabolicVelocity T τ a U r ∂volume) := by
  apply circle_fourier_ext T
  intro n
  let L := parabolicFourierFunctional T n
  let y₀ := L (circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ U 0))
  let f : ℝ → ℂ := fun x =>
    τ • unitTimeZeroExtend (fun r => L (circleParabolicTimeDerivative T τ U r)) x
  let z : ℂ := circleFrequencyFactor T n*(a:ℂ)
  let y : ℝ → ℂ := fun x => y₀+∫ r in (0:ℝ)..x, f r
  let g : ℝ → ℂ := fun x =>
    Complex.exp (z*(x:ℂ))*f x+z*Complex.exp (z*(x:ℂ))*y x
  have hy (r : unitInterval) : y (r:ℝ) =
      L (circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ U r)) :=
    parabolic_fourier_primitive T τ U n r
  have hf : IntervalIntegrable f volume (0:ℝ) 1 :=
    (parabolic_scalar_velocity_zero_extend_integrable T τ U L).intervalIntegrable
  have hphase : Complex.exp (z*((t:ℝ):ℂ))*y (t:ℝ)-y₀ =
      ∫ r in (0:ℝ)..(t:ℝ), g r :=
    complex_phase_primitive f hf y₀ z (t:ℝ) t.property
  have hshift (r : unitInterval) :
      L (circleSobolevCoordinate T 2 0 (translatedParabolicCurve T τ a U r)) =
        Complex.exp (z*((r:ℝ):ℂ))*y (r:ℝ) := by
    have hs := parabolic_fourier_shift_coordinate T 2 n (a*(r:ℝ))
      (circleParabolicCurve T τ U r) 0
    have hc := translation_fourier_phase T n a (r:ℝ)
    exact hs.trans (congrArg₂ (fun u v : ℂ => u*v) hc (hy r).symm)
  have hinit : L (circleSobolevCoordinate T 2 0 (translatedParabolicCurve T τ a U 0)) = y₀ := by
    simpa only [y,Set.Icc.coe_zero,mul_zero,Complex.ofReal_zero,Complex.exp_zero,
      intervalIntegral.integral_same,add_zero,one_mul] using hshift (0 : unitInterval)
  have hg : ∀ᵐ r : unitInterval ∂volume,
      g (r:ℝ) = τ • L (translatedParabolicVelocity T τ a U r) := by
    filter_upwards [translated_parabolic_velocity_ae T τ a U,
      circle_parabolic_value_ae T τ U] with r hvel hvalue
    let phase : ℂ := Complex.exp (z*((r:ℝ):ℂ))
    let ν : ℂ := circleFrequencyFactor T n
    let v₀ : ℂ := L (circleParabolicTimeDerivative T τ U r)
    let H := circleParabolicH4 T τ U r
    let Hshift := realSobolevShift T 4 (a*(r:ℝ)) H
    have hchar : fourier n ((a*(r:ℝ):ℝ) : AddCircle T) = phase :=
      translation_fourier_phase T n a (r:ℝ)
    have hzero : L (circleSobolevCoordinate T 4 0 Hshift) = phase*y (r:ℝ) := by
      have hs := parabolic_fourier_shift_coordinate T 4 n (a*(r:ℝ)) H 0
      have hy' : L (circleSobolevCoordinate T 4 0 H) = y (r:ℝ) :=
        (congrArg L hvalue.symm).trans (hy r).symm
      exact hs.trans (congrArg₂ (fun u v : ℂ => u*v) hchar hy')
    have hD : L (circleSobolevCoordinate T 4 1 Hshift) = ν*phase*y (r:ℝ) :=
      (parabolic_fourier_functional_deriv T n Hshift).trans
        ((congrArg (fun v : ℂ => ν*v) hzero).trans ((mul_assoc ν phase (y (r:ℝ))).symm))
    have hW : L (realCircleL2Shift T (a*(r:ℝ)) (circleParabolicTimeDerivative T τ U r)) =
        phase*v₀ :=
      (parabolic_fourier_functional_shift T n ((a*(r:ℝ):ℝ) : AddCircle T) _).trans
        (congrArg (fun p : ℂ => p*v₀) hchar)
    have hV : L (translatedParabolicVelocity T τ a U r) =
        phase*v₀+((a/τ:ℝ):ℂ)*(ν*phase*y (r:ℝ)) :=
      (congrArg L hvel).trans
        ((complex_linear_pair L _ _ ((a/τ:ℝ):ℂ)).trans
          (congrArg₂ (fun p q : ℂ => p+((a/τ:ℝ):ℂ)*q) hW hD))
    have hfr : f (r:ℝ) = τ • v₀ :=
      congrArg (fun v : ℂ => τ • v)
        (unit_time_zero_extend_apply (fun r => L (circleParabolicTimeDerivative T τ U r)) r)
    have hG : g (r:ℝ) = phase*(τ • v₀)+z*phase*y (r:ℝ) :=
      congrArg (fun v : ℂ => phase*v+z*phase*y (r:ℝ)) hfr
    exact hG.trans ((physical_phase_integrand τ a hτ ν phase (y (r:ℝ)) v₀).trans
      (congrArg (fun v : ℂ => τ • v) hV).symm)

  have hgIntegral : (∫ r in (0:ℝ)..(t:ℝ), g r) =
      τ • (∫ r in Iic t, L (translatedParabolicVelocity T τ a U r) ∂volume) := by
    rw [← unit_interval_setIntegral g t]
    calc
      (∫ r in Iic t, g (r:ℝ) ∂volume) =
          ∫ r in Iic t, τ • L (translatedParabolicVelocity T τ a U r) ∂volume :=
        integral_congr_ae (ae_restrict_of_ae hg)
      _ = _ := integral_smul τ _
  have hvint : Integrable (translatedParabolicVelocity T τ a U)
      (volume : Measure unitInterval) :=
    memLp_one_iff_integrable.mp
      ((Lp.memLp (translatedParabolicVelocity T τ a U)).mono_exponent
        (by norm_num : (1:ℝ≥0∞) ≤ 2))
  have hLIntegral : L (τ • (∫ r in Iic t, translatedParabolicVelocity T τ a U r ∂volume)) =
      τ • (∫ r in Iic t, L (translatedParabolicVelocity T τ a U r) ∂volume) := by
    change (L.restrictScalars ℝ) (τ • (∫ r in Iic t, translatedParabolicVelocity T τ a U r ∂volume)) = _
    rw [map_smul,← (L.restrictScalars ℝ).integral_comp_comm hvint.integrableOn]
    rfl
  have hL : L (circleSobolevCoordinate T 2 0 (translatedParabolicCurve T τ a U t)-
      circleSobolevCoordinate T 2 0 (translatedParabolicCurve T τ a U 0)) =
      L (τ • (∫ r in Iic t, translatedParabolicVelocity T τ a U r ∂volume)) := by
    rw [map_sub,hshift t,hinit,hLIntegral]
    exact hphase.trans hgIntegral
  simpa only [L,parabolic_fourier_functional_apply] using! hL


set_option maxHeartbeats 600000 in
/-- Spatial translation by a*t on the actual parabolic solution space.
The velocity is the physical velocity, so its transport term is (a/tau)*D_x.
The new primitive constraint follows from the complex Fourier phase rule. -/
def circleParabolicTranslation (hτ : τ ≠ 0) (a : ℝ) (U : CircleParabolicSpace T τ) :
    CircleParabolicSpace T τ :=
  ⟨translatedParabolicAmbient T τ a U,
    parabolic_membership_of_representatives T τ
      (translatedParabolicCurve T τ a U) (translatedParabolicH4 T τ a U)
      (translatedParabolicVelocity T τ a U) (translated_parabolic_value_ae T τ a U)
      (translated_parabolic_primitive T τ hτ a U)⟩

@[simp] theorem circle_parabolic_translation_curve (hτ : τ ≠ 0) (a : ℝ)
    (U : CircleParabolicSpace T τ) (t : unitInterval) :
    circleParabolicCurve T τ (circleParabolicTranslation T τ hτ a U) t =
      circleSobolevTranslation T 2 ((a*(t:ℝ):ℝ) : AddCircle T)
        (circleParabolicCurve T τ U t) := rfl

/-- The H4 and physical-velocity representatives are the actual translated
jets almost everywhere; translation fixes the initial H2 datum. -/
theorem circle_parabolic_translation_components (hτ : τ ≠ 0) (a : ℝ)
    (U : CircleParabolicSpace T τ) :
    ((circleParabolicH4 T τ (circleParabolicTranslation T τ hτ a U) :
        unitInterval → CircleSobolevSpace T 4) =ᵐ[volume]
      fun t => circleSobolevTranslation T 4 ((a*(t:ℝ):ℝ) : AddCircle T)
        (circleParabolicH4 T τ U t)) ∧
    ((circleParabolicTimeDerivative T τ (circleParabolicTranslation T τ hτ a U) :
        unitInterval → CircleL2 T) =ᵐ[volume]
      fun t => circleL2Translation T ((a*(t:ℝ):ℝ) : AddCircle T)
          (circleParabolicTimeDerivative T τ U t)+
        ((a/τ:ℝ):ℂ) • circleSobolevCoordinate T 4 1
          (circleSobolevTranslation T 4 ((a*(t:ℝ):ℝ) : AddCircle T)
            (circleParabolicH4 T τ U t))) ∧
    circleParabolicInitialValue T τ (circleParabolicTranslation T τ hτ a U) =
      circleParabolicInitialValue T τ U := by
  refine ⟨?_,translated_parabolic_velocity_ae T τ a U,?_⟩
  · exact lp_time_transport_ae (realSobolevShift T 4) (real_sobolev_shift_continuous T 4)
      a (circleParabolicH4 T τ U)
  · change circleSobolevTranslation T 2 ((a*(0:ℝ):ℝ) : AddCircle T)
      (circleParabolicCurve T τ U 0) = circleParabolicCurve T τ U 0
    simpa only [mul_zero,AddCircle.coe_zero] using
      circle_sobolev_translation_zero T 2 (circleParabolicCurve T τ U 0)

/-- Strong continuity in the translation parameter holds in the full
parabolic norm, including the true L2-in-time H4 and velocity components. -/
theorem circle_parabolic_translation_continuous (hτ : τ ≠ 0)
    (U : CircleParabolicSpace T τ) :
    Continuous (fun a : ℝ => circleParabolicTranslation T τ hτ a U) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply tendsto_subtype_rng.mpr
  exact (translated_parabolic_components_continuous T τ U).continuousAt

end Lemniscate
