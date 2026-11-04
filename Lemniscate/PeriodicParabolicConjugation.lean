import Lemniscate.PeriodicParabolicSpace
import Lemniscate.PeriodicSobolevConjugation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.ContinuousMap.Algebra

/-! Real linear isometric conjugation on the actual closed parabolic space.

Both closed constraints are preserved. In particular the physical velocity
and the continuous curve remain related by the same Bochner primitive,
because real linear conjugation commutes with integration and real tau.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal Topology ComplexConjugate

private def conjugationTimeLift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : E ≃ₗᵢ[ℝ] E) (hJ : Function.Involutive J) :
    Lp E 2 (volume : Measure unitInterval) ≃ₗᵢ[ℝ]
      Lp E 2 (volume : Measure unitInterval) := by
  let A := J.toContinuousLinearEquiv.toContinuousLinearMap.compLpL
    2 (volume : Measure unitInterval)
  have hinvol (f : Lp E 2 (volume : Measure unitInterval)) : A (A f) = f := by
    apply Lp.ext
    filter_upwards [J.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL
      (p := 2) (μ := (volume : Measure unitInterval)) (A f),
      J.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL
        (p := 2) (μ := (volume : Measure unitInterval)) f] with t ht hf
    exact ht.trans ((congrArg J hf).trans (hJ (f t)))
  have hnorm (f : Lp E 2 (volume : Measure unitInterval)) : ‖A f‖ = ‖f‖ := by
    have hpoint : ∀ᵐ t ∂(volume : Measure unitInterval), ‖A f t‖ = ‖f t‖ := by
      filter_upwards [J.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL
        (p := 2) (μ := (volume : Measure unitInterval)) f] with t ht
      exact (congrArg norm ht).trans (J.norm_map (f t))
    exact le_antisymm (Lp.norm_le_norm_of_ae_le (hpoint.mono fun _ h => h.le))
      (Lp.norm_le_norm_of_ae_le (hpoint.mono fun _ h => h.ge))
  exact
    { toFun := A
      invFun := A
      left_inv := hinvol
      right_inv := hinvol
      map_add' := A.map_add
      map_smul' := A.map_smul
      norm_map' := hnorm }

private theorem conjugation_time_lift_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : E ≃ₗᵢ[ℝ] E) (hJ : Function.Involutive J)
    (f : Lp E 2 (volume : Measure unitInterval)) :
    (conjugationTimeLift J hJ f : unitInterval → E) =ᵐ[volume] fun t => J (f t) :=
  J.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL f

private def conjugationCurveLift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : E ≃ₗᵢ[ℝ] E) (hJ : Function.Involutive J) :
    C(unitInterval,E) ≃ₗᵢ[ℝ] C(unitInterval,E) := by
  let A := J.toContinuousLinearEquiv.toContinuousLinearMap.compLeftContinuous ℝ unitInterval
  have hinvol (f : C(unitInterval,E)) : A (A f) = f := by
    apply ContinuousMap.ext
    intro t
    exact hJ (f t)
  have hnorm (f : C(unitInterval,E)) : ‖A f‖ = ‖f‖ := by
    have h₁ : ‖A f‖ ≤ ‖f‖ := (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun t => by
      change ‖J (f t)‖ ≤ ‖f‖
      rw [J.norm_map]
      exact f.norm_coe_le_norm t
    have h₂ : ‖f‖ ≤ ‖A f‖ := (f.norm_le (norm_nonneg _)).mpr fun t => by
      have h := (A f).norm_coe_le_norm t
      change ‖J (f t)‖ ≤ ‖A f‖ at h
      simpa only [J.norm_map] using h
    exact le_antisymm h₁ h₂
  exact
    { toFun := A
      invFun := A
      left_inv := hinvol
      right_inv := hinvol
      map_add' := A.map_add
      map_smul' := A.map_smul
      norm_map' := hnorm }

variable (T : ℝ) [Fact (0 < T)]

private def parabolicSpatialL2Conjugation : CircleL2 T ≃ₗᵢ[ℝ] CircleL2 T where
  toFun := circleConjugate T
  invFun := circleConjugate T
  left_inv := circle_conjugate_involutive T
  right_inv := circle_conjugate_involutive T
  map_add' := circle_conjugate_add T
  map_smul' r f := by
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),circle_conjugate_smul,
      RCLike.conj_ofReal,RingHom.id_apply]
  norm_map' f := by
    change ‖circleConjugate T f‖ = ‖f‖
    have hsq : ‖circleConjugate T f‖^2 = ‖f‖^2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ),norm_sq_eq_re_inner (𝕜 := ℂ),circle_conjugate_inner]
      exact Complex.conj_re _
    nlinarith only [hsq,norm_nonneg f,norm_nonneg (circleConjugate T f)]

private def parabolicCurveConjugation :
    C(unitInterval,CircleSobolevSpace T 2) ≃ₗᵢ[ℝ] C(unitInterval,CircleSobolevSpace T 2) :=
  conjugationCurveLift (circleSobolevConjugation T 2) (circle_sobolev_conjugation_involutive T 2)

private def parabolicH4Conjugation : CircleTimeH4 T ≃ₗᵢ[ℝ] CircleTimeH4 T :=
  conjugationTimeLift (circleSobolevConjugation T 4) (circle_sobolev_conjugation_involutive T 4)

private def parabolicVelocityConjugation : CircleTimeL2 T ≃ₗᵢ[ℝ] CircleTimeL2 T :=
  conjugationTimeLift (parabolicSpatialL2Conjugation T) (circle_conjugate_involutive T)

variable (τ : ℝ)

local instance parabolicConjugationTimeSecondCountable :
    SecondCountableTopologyEither unitInterval (CircleSobolevSpace T 2) where
  out := Or.inl (inferInstance : SecondCountableTopology unitInterval)

set_option maxHeartbeats 1200000 in
private theorem parabolic_conjugation_mem (U : CircleParabolicSpace T τ) :
    (parabolicCurveConjugation T (circleParabolicCurve T τ U),
      (parabolicH4Conjugation T (circleParabolicH4 T τ U),
        parabolicVelocityConjugation T (circleParabolicTimeDerivative T τ U))) ∈
      circleParabolicSubmodule T τ := by
  let C := circleParabolicCurve T τ U
  let H := circleParabolicH4 T τ U
  let V := circleParabolicTimeDerivative T τ U
  let Cstar := parabolicCurveConjugation T C
  let Hstar := parabolicH4Conjugation T H
  let Vstar := parabolicVelocityConjugation T V
  let J := (parabolicSpatialL2Conjugation T).toContinuousLinearEquiv.toContinuousLinearMap
  have hC (t : unitInterval) : Cstar t = circleSobolevConjugation T 2 (C t) := rfl
  have hH : (Hstar : unitInterval → CircleSobolevSpace T 4) =ᵐ[volume]
      fun t => circleSobolevConjugation T 4 (H t) :=
    conjugation_time_lift_ae _ _ H
  have hV : (Vstar : unitInterval → CircleL2 T) =ᵐ[volume]
      fun t => circleConjugate T (V t) := conjugation_time_lift_ae _ _ V
  apply (circle_parabolic_mem_iff T τ _).mpr
  constructor
  · apply Lp.ext
    have hc := (circleSobolevCoordinate T 2 0).coeFn_compLpL
      (p := 2) (μ := (volume : Measure unitInterval))
      (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℂ Cstar)
    have hct := ContinuousMap.coeFn_toLp (p := 2) (volume : Measure unitInterval) (𝕜 := ℂ) Cstar
    have hh := (circleSobolevCoordinate T 4 0).coeFn_compLpL
      (p := 2) (μ := (volume : Measure unitInterval)) Hstar
    filter_upwards [hc,hct,hh,hH,circle_parabolic_value_ae T τ U]
      with t hcp hctp hhp hHt hvalue
    exact hcp.trans ((congrArg (circleSobolevCoordinate T 2 0) hctp).trans
      ((congrArg (circleSobolevCoordinate T 2 0) (hC t)).trans
        ((circle_sobolev_conjugation_coordinate T 2 0 (C t)).trans
          ((congrArg (circleConjugate T) hvalue).trans
            ((circle_sobolev_conjugation_coordinate T 4 0 (H t)).symm.trans
              ((congrArg (circleSobolevCoordinate T 4 0) hHt).symm.trans hhp.symm))))))
  · intro t
    have hInt : (∫ r in Iic t, circleConjugate T (V r) ∂volume) =
        J (∫ r in Iic t, V r ∂volume) :=
      J.integral_comp_comm ((circle_parabolic_time_derivative_integrable T τ U).mono_measure
        Measure.restrict_le_self)
    have hVInt : (∫ r in Iic t, Vstar r ∂volume) =
        ∫ r in Iic t, circleConjugate T (V r) ∂volume :=
      integral_congr_ae (ae_restrict_of_ae hV)
    have hOriginal := circle_parabolic_integral_identity T τ U t
    change circleSobolevCoordinate T 2 0 (Cstar t)-
      circleSobolevCoordinate T 2 0 (Cstar 0) = τ • (∫ r in Iic t, Vstar r ∂volume)
    calc
      circleSobolevCoordinate T 2 0 (Cstar t)-circleSobolevCoordinate T 2 0 (Cstar 0) =
          J (circleSobolevCoordinate T 2 0 (C t)-circleSobolevCoordinate T 2 0 (C 0)) := by
        rw [hC,hC,circle_sobolev_conjugation_coordinate,circle_sobolev_conjugation_coordinate]
        exact (J.map_sub _ _).symm
      _ = J (τ • (∫ r in Iic t, V r ∂volume)) := congrArg J hOriginal
      _ = τ • J (∫ r in Iic t, V r ∂volume) := J.map_smul τ _
      _ = τ • (∫ r in Iic t, Vstar r ∂volume) := congrArg (fun z : CircleL2 T => τ • z)
        (hVInt.trans hInt).symm

set_option maxHeartbeats 1000000 in
private def parabolicConjugateLinear : CircleParabolicSpace T τ →ₗ[ℝ] CircleParabolicSpace T τ where
  toFun U := ⟨(parabolicCurveConjugation T (circleParabolicCurve T τ U),
    (parabolicH4Conjugation T (circleParabolicH4 T τ U),
      parabolicVelocityConjugation T (circleParabolicTimeDerivative T τ U))),
      parabolic_conjugation_mem T τ U⟩
  map_add' U V := by
    apply Subtype.ext
    apply Prod.ext
    · exact (congrArg (parabolicCurveConjugation T)
        ((circleParabolicCurve T τ).map_add U V)).trans (map_add _ _ _)
    · apply Prod.ext
      · exact (congrArg (parabolicH4Conjugation T)
          ((circleParabolicH4 T τ).map_add U V)).trans (map_add _ _ _)
      · exact (congrArg (parabolicVelocityConjugation T)
          ((circleParabolicTimeDerivative T τ).map_add U V)).trans (map_add _ _ _)
  map_smul' r U := by
    apply Subtype.ext
    apply Prod.ext
    · change parabolicCurveConjugation T (circleParabolicCurve T τ (r • U)) =
        r • parabolicCurveConjugation T (circleParabolicCurve T τ U)
      exact (congrArg (parabolicCurveConjugation T)
        (((circleParabolicCurve T τ).restrictScalars ℝ).map_smul r U)).trans (map_smul _ _ _)
    · apply Prod.ext
      · exact (congrArg (parabolicH4Conjugation T)
          (((circleParabolicH4 T τ).restrictScalars ℝ).map_smul r U)).trans (map_smul _ _ _)
      · exact (congrArg (parabolicVelocityConjugation T)
          (((circleParabolicTimeDerivative T τ).restrictScalars ℝ).map_smul r U)).trans (map_smul _ _ _)

set_option maxHeartbeats 1000000 in
private theorem parabolic_conjugate_involutive (U : CircleParabolicSpace T τ) :
    parabolicConjugateLinear T τ (parabolicConjugateLinear T τ U) = U := by
  apply Subtype.ext
  apply Prod.ext
  · exact (parabolicCurveConjugation T).left_inv U.1.1
  · apply Prod.ext
    · exact (parabolicH4Conjugation T).left_inv U.1.2.1
    · exact (parabolicVelocityConjugation T).left_inv U.1.2.2

set_option maxHeartbeats 1000000 in
private theorem parabolic_conjugate_norm (U : CircleParabolicSpace T τ) :
    ‖parabolicConjugateLinear T τ U‖ = ‖U‖ := by
  change max ‖parabolicCurveConjugation T U.1.1‖
    (max ‖parabolicH4Conjugation T U.1.2.1‖ ‖parabolicVelocityConjugation T U.1.2.2‖) =
    max ‖U.1.1‖ (max ‖U.1.2.1‖ ‖U.1.2.2‖)
  have hC : ‖parabolicCurveConjugation T U.1.1‖ = ‖U.1.1‖ :=
    (parabolicCurveConjugation T).norm_map U.1.1
  have hH : ‖parabolicH4Conjugation T U.1.2.1‖ = ‖U.1.2.1‖ :=
    (parabolicH4Conjugation T).norm_map U.1.2.1
  have hV : ‖parabolicVelocityConjugation T U.1.2.2‖ = ‖U.1.2.2‖ :=
    (parabolicVelocityConjugation T).norm_map U.1.2.2
  exact congrArg₂ (fun a b : ℝ => max a b) hC
    (congrArg₂ (fun a b : ℝ => max a b) hH hV)

set_option maxHeartbeats 1000000 in
/-- Conjugation on the actual parabolic space, as a real linear isometric involution. -/
def circleParabolicConjugation : CircleParabolicSpace T τ ≃ₗᵢ[ℝ] CircleParabolicSpace T τ where
  toFun := parabolicConjugateLinear T τ
  invFun := parabolicConjugateLinear T τ
  left_inv := parabolic_conjugate_involutive T τ
  right_inv := parabolic_conjugate_involutive T τ
  map_add' := (parabolicConjugateLinear T τ).map_add
  map_smul' := (parabolicConjugateLinear T τ).map_smul
  norm_map' := parabolic_conjugate_norm T τ

set_option maxHeartbeats 1000000 in
/-- The curve, H4 representative, physical velocity and initial value all
have their actual pointwise or almost-everywhere conjugation meanings. -/
theorem circle_parabolic_conjugation_components (U : CircleParabolicSpace T τ) :
    (∀ t : unitInterval, circleParabolicCurve T τ (circleParabolicConjugation T τ U) t =
      circleSobolevConjugation T 2 (circleParabolicCurve T τ U t)) ∧
    (∀ᵐ t : unitInterval ∂volume, circleParabolicH4 T τ (circleParabolicConjugation T τ U) t =
      circleSobolevConjugation T 4 (circleParabolicH4 T τ U t)) ∧
    (∀ᵐ t : unitInterval ∂volume,
      circleParabolicTimeDerivative T τ (circleParabolicConjugation T τ U) t =
        circleConjugate T (circleParabolicTimeDerivative T τ U t)) ∧
    circleParabolicInitialValue T τ (circleParabolicConjugation T τ U) =
      circleSobolevConjugation T 2 (circleParabolicInitialValue T τ U) := by
  refine ⟨fun t => rfl,
    conjugation_time_lift_ae (circleSobolevConjugation T 4)
      (circle_sobolev_conjugation_involutive T 4) (circleParabolicH4 T τ U),
    conjugation_time_lift_ae (parabolicSpatialL2Conjugation T)
      (circle_conjugate_involutive T) (circleParabolicTimeDerivative T τ U),?_⟩
  rfl

end Lemniscate
