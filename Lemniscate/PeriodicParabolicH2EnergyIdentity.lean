import Lemniscate.PeriodicParabolicEnergyIdentity
import Lemniscate.PeriodicSobolevFourierProjection
import Lemniscate.PeriodicSobolevFourierPolynomial
import Lemniscate.PeriodicIntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Logic.Equiv.List

/-! The fourth-order principal energy identity on the actual parabolic space.

The time derivative of two spatial derivatives need not belong to L2.
Finite Fourier truncations make this derivative bounded on L2.  Their
primitive energy identities pass to the limit by strong Fourier convergence
and scalar dominated convergence.  No equation or classical time regularity
is assumed.


-/

noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology

variable (T : ℝ) [Fact (0 < T)]

private def finiteFourierLift (m : ℕ) (I : Finset ℤ) :
    CircleL2 T →L[ℂ] CircleSobolevSpace T m :=
  ∑ n ∈ I, (innerSL ℂ (fourierBasis (T := T) n)).smulRight
    (circleSobolevFourierMode T m n)

private theorem finite_fourier_lift_coordinate (m : ℕ) (I : Finset ℤ)
    (f : CircleL2 T) (j : Fin (m+1)) :
    circleSobolevCoordinate T m j (finiteFourierLift T m I f) =
      ∑ n ∈ I, (fourierCoeff f n * (circleFrequencyFactor T n)^j.val) •
        fourierBasis (T := T) n := by
  have hc (n : ℤ) : inner ℂ (fourierBasis (T := T) n) f = fourierCoeff f n := by
    rw [← HilbertBasis.repr_apply_apply,fourierBasis_repr]
  simp only [finiteFourierLift,sum_apply,ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply,map_sum,map_smul,circle_sobolev_fourier_mode_coordinate,
    hc,smul_smul]

private theorem finite_fourier_lift_value (m : ℕ) (I : Finset ℤ)
    (f : CircleL2 T) :
    circleSobolevCoordinate T m 0 (finiteFourierLift T m I f) =
      circleFourierProjection T I f := by
  rw [finite_fourier_lift_coordinate,circle_fourier_projection_apply]
  simp only [Fin.val_zero,pow_zero,mul_one]

private theorem finite_fourier_lift_projected_coordinate (m : ℕ) (I : Finset ℤ)
    (f : CircleSobolevSpace T m) (j : Fin (m+1)) :
    circleSobolevCoordinate T m j
        (finiteFourierLift T m I (circleSobolevCoordinate T m 0 f)) =
      circleFourierProjection T I (circleSobolevCoordinate T m j f) := by
  have h : finiteFourierLift T m I (circleSobolevCoordinate T m 0 f) =
      circleSobolevFourierProjection T m I f := by
    apply circle_sobolev_value_injective T m
    rw [finite_fourier_lift_value,circle_sobolev_fourier_projection_coordinate,
      circle_fourier_projection_apply]
  rw [h,circle_sobolev_fourier_projection_coordinate,circle_fourier_projection_apply]

private def finiteSecondDerivative (I : Finset ℤ) : CircleL2 T →L[ℂ] CircleL2 T :=
  (circleSobolevCoordinate T 4 2).comp (finiteFourierLift T 4 I)

private theorem finite_second_derivative_h2 (I : Finset ℤ)
    (f : CircleSobolevSpace T 2) :
    finiteSecondDerivative T I (circleSobolevCoordinate T 2 0 f) =
      circleFourierProjection T I (circleSobolevCoordinate T 2 2 f) := by
  calc
    finiteSecondDerivative T I (circleSobolevCoordinate T 2 0 f) =
        circleSobolevCoordinate T 2 2
          (finiteFourierLift T 2 I (circleSobolevCoordinate T 2 0 f)) := by
      change circleSobolevCoordinate T 4 2
        (finiteFourierLift T 4 I (circleSobolevCoordinate T 2 0 f)) = _
      rw [finite_fourier_lift_coordinate,finite_fourier_lift_coordinate]
      apply Finset.sum_congr rfl
      intro n _
      rfl
    _ = circleFourierProjection T I (circleSobolevCoordinate T 2 2 f) :=
      finite_fourier_lift_projected_coordinate T 2 I f 2

private theorem fourth_second_green (f g : CircleSobolevSpace T 4) :
    inner ℂ (circleSobolevCoordinate T 4 2 f) (circleSobolevCoordinate T 4 2 g) =
      inner ℂ (circleSobolevCoordinate T 4 4 f) (circleSobolevCoordinate T 4 0 g) := by
  have ha : inner ℂ (circleSobolevCoordinate T 4 4 f) (circleSobolevCoordinate T 4 0 g) =
      -inner ℂ (circleSobolevCoordinate T 4 3 f) (circleSobolevCoordinate T 4 1 g) := by
    simpa only [circle_sobolev_coordinate_apply] using!
      (circle_weak_integration_by_parts T _ _ _ _
        (circle_sobolev_weak_deriv T 4 f 3) (circle_sobolev_weak_deriv T 4 g 0))
  have hb : inner ℂ (circleSobolevCoordinate T 4 3 f) (circleSobolevCoordinate T 4 1 g) =
      -inner ℂ (circleSobolevCoordinate T 4 2 f) (circleSobolevCoordinate T 4 2 g) := by
    simpa only [circle_sobolev_coordinate_apply] using!
      (circle_weak_integration_by_parts T _ _ _ _
        (circle_sobolev_weak_deriv T 4 f 2) (circle_sobolev_weak_deriv T 4 g 1))
  calc
    inner ℂ (circleSobolevCoordinate T 4 2 f) (circleSobolevCoordinate T 4 2 g) =
        -inner ℂ (circleSobolevCoordinate T 4 3 f) (circleSobolevCoordinate T 4 1 g) := by
      rw [hb,neg_neg]
    _ = inner ℂ (circleSobolevCoordinate T 4 4 f) (circleSobolevCoordinate T 4 0 g) := by
      exact ha.symm

private theorem finite_second_pairing (I : Finset ℤ)
    (f : CircleSobolevSpace T 4) (v : CircleL2 T) :
    inner ℂ (finiteSecondDerivative T I (circleSobolevCoordinate T 4 0 f))
        (finiteSecondDerivative T I v) =
      inner ℂ (circleFourierProjection T I (circleSobolevCoordinate T 4 4 f))
        (circleFourierProjection T I v) := by
  change inner ℂ
    (circleSobolevCoordinate T 4 2
      (finiteFourierLift T 4 I (circleSobolevCoordinate T 4 0 f)))
    (circleSobolevCoordinate T 4 2 (finiteFourierLift T 4 I v)) = _
  rw [fourth_second_green,finite_fourier_lift_projected_coordinate,
    finite_fourier_lift_value]

private theorem finite_second_pairing_values (I : Finset ℤ)
    (f : CircleSobolevSpace T 4) (q g v : CircleL2 T)
    (hq : q = circleSobolevCoordinate T 4 0 f)
    (hg : g = circleSobolevCoordinate T 4 4 f) :
    (inner ℂ (finiteSecondDerivative T I q) (finiteSecondDerivative T I v)).re =
      (inner ℂ (circleFourierProjection T I g) (circleFourierProjection T I v)).re := by
  subst q
  subst g
  exact congrArg Complex.re (finite_second_pairing T I f v)

private theorem projection_norm_le (I : Finset ℤ) (f : CircleL2 T) :
    ‖circleFourierProjection T I f‖ ≤ ‖f‖ := by
  simpa only [one_mul] using
    (circleFourierProjection T I).le_of_opNorm_le (circle_fourier_projection_norm_le T I) f

private theorem projected_inner_integral_tendsto
    (G V : CircleTimeL2 T) (t : unitInterval) :
    Tendsto (fun I : Finset ℤ => ∫ r in Iic t,
      (inner ℂ (circleFourierProjection T I (G r))
        (circleFourierProjection T I (V r))).re ∂volume) atTop
      (𝓝 (∫ r in Iic t, (inner ℂ (G r) (V r)).re ∂volume)) := by
  have hGsq : Integrable (fun r : unitInterval => ‖G r‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable G)).mp (Lp.memLp G)
  have hVsq : Integrable (fun r : unitInterval => ‖V r‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable V)).mp (Lp.memLp V)
  have hm (I : Finset ℤ) : AEStronglyMeasurable (fun r : unitInterval =>
      (inner ℂ (circleFourierProjection T I (G r))
        (circleFourierProjection T I (V r))).re) volume := by
    simpa only [RCLike.re_eq_complex_re] using
      ((((circleFourierProjection T I).continuous.comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable G)).inner (𝕜 := ℂ)
        ((circleFourierProjection T I).continuous.comp_aestronglyMeasurable
          (Lp.aestronglyMeasurable V))).re)
  have hb (I : Finset ℤ) (r : unitInterval) :
      ‖(inner ℂ (circleFourierProjection T I (G r))
        (circleFourierProjection T I (V r))).re‖ ≤ ‖G r‖^2+‖V r‖^2 := by
    calc
      _ ≤ ‖inner ℂ (circleFourierProjection T I (G r))
          (circleFourierProjection T I (V r))‖ := by
        rw [Real.norm_eq_abs]
        exact Complex.abs_re_le_norm _
      _ ≤ ‖circleFourierProjection T I (G r)‖ * ‖circleFourierProjection T I (V r)‖ :=
        norm_inner_le_norm _ _
      _ ≤ ‖G r‖ * ‖V r‖ := mul_le_mul (projection_norm_le T I _)
        (projection_norm_le T I _) (norm_nonneg _) (norm_nonneg _)
      _ ≤ ‖G r‖^2+‖V r‖^2 := by nlinarith [sq_nonneg (‖G r‖-‖V r‖)]
  apply tendsto_integral_filter_of_dominated_convergence
    (fun r : unitInterval => ‖G r‖^2+‖V r‖^2)
    (Eventually.of_forall (fun I => (hm I).restrict))
    (Eventually.of_forall (fun I => Eventually.of_forall (hb I)))
    ((hGsq.add hVsq).integrableOn)
  exact Eventually.of_forall fun r =>
    Complex.continuous_re.continuousAt.tendsto.comp
      ((circle_fourier_projection_tendsto T (G r)).inner
        (circle_fourier_projection_tendsto T (V r)))

private theorem integral_re_inner_four
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (q w v : unitInterval → E) (t : unitInterval)
    (h0 : Integrable (fun r => (inner ℂ (q r) (v r)).re) volume)
    (h4 : Integrable (fun r => (inner ℂ (w r) (v r)).re) volume) :
    (∫ r in Iic t, (inner ℂ (q r+(4:ℂ) • w r) (v r)).re ∂volume) =
      (∫ r in Iic t, (inner ℂ (q r) (v r)).re ∂volume)+
        4*(∫ r in Iic t, (inner ℂ (w r) (v r)).re ∂volume) := by
  simp_rw [inner_add_left,inner_smul_left,map_ofNat,Complex.add_re,Complex.mul_re]
  simp only [Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
  rw [integral_add h0.integrableOn (h4.const_mul 4).integrableOn,integral_const_mul]

private theorem combine_quadratic_energy
    {a₀ a₁ b₀ b₁ E₀ E₂ τ : ℝ}
    (h0 : a₁-a₀ = (2*τ)*E₀) (h2 : b₁-b₀ = (2*τ)*E₂) :
    (a₁+4*b₁)-(a₀+4*b₀) = (2*τ)*(E₀+4*E₂) := by
  linear_combination h0+4*h2

variable (τ : ℝ)

set_option maxHeartbeats 600000 in
private theorem parabolic_second_energy (U : CircleParabolicSpace T τ)
    (t : unitInterval) :
    ‖circleSobolevCoordinate T 2 2 (circleParabolicCurve T τ U t)‖^2-
        ‖circleSobolevCoordinate T 2 2 (circleParabolicCurve T τ U 0)‖^2 =
      (2*τ) * ∫ r in Iic t,
        (inner ℂ (circleSobolevCoordinate T 4 4 (circleParabolicH4 T τ U r))
          (circleParabolicTimeDerivative T τ U r)).re ∂volume := by
  let q : unitInterval → CircleL2 T :=
    fun r => circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ U r)
  let d : unitInterval → CircleL2 T :=
    fun r => circleSobolevCoordinate T 2 2 (circleParabolicCurve T τ U r)
  let V : CircleTimeL2 T := circleParabolicTimeDerivative T τ U
  let G : CircleTimeL2 T := (circleSobolevCoordinate T 4 4).compLpL 2
    (volume : Measure unitInterval) (circleParabolicH4 T τ U)
  have hG := (circleSobolevCoordinate T 4 4).coeFn_compLpL
    (p := 2) (μ := (volume : Measure unitInterval)) (circleParabolicH4 T τ U)
  have hV : Integrable (V : unitInterval → CircleL2 T) volume :=
    circle_parabolic_time_derivative_integrable T τ U
  have hfinite (I : Finset ℤ) :
      ‖circleFourierProjection T I (d t)‖^2-
          ‖circleFourierProjection T I (d 0)‖^2 =
        (2*τ) * ∫ r in Iic t,
          (inner ℂ (circleFourierProjection T I (G r))
            (circleFourierProjection T I (V r))).re ∂volume := by
    let D : CircleL2 T →L[ℂ] CircleL2 T := finiteSecondDerivative T I
    have hprimitive (r : unitInterval) : D (q r)-D (q 0) =
        τ • (∫ s in Iic r, D (V s) ∂volume) := by
      have hp := circle_parabolic_integral_identity T τ U r
      calc
        D (q r)-D (q 0) = D (q r-q 0) := (map_sub D _ _).symm
        _ = D (τ • (∫ s in Iic r, V s ∂volume)) := congrArg D hp
        _ = τ • (∫ s in Iic r, D (V s) ∂volume) := by
          change (D.restrictScalars ℝ) (τ • (∫ s in Iic r, V s ∂volume)) = _
          rw [(D.restrictScalars ℝ).map_smul,
            ← (D.restrictScalars ℝ).integral_comp_comm hV.integrableOn]
          simp only [ContinuousLinearMap.coe_restrictScalars']
    have he := unit_interval_primitive_norm_sq_energy τ
      (fun r => D (q r)) (fun r => D (V r)) (D.integrable_comp hV) hprimitive t
    have heval (r : unitInterval) : D (q r) = circleFourierProjection T I (d r) :=
      finite_second_derivative_h2 T I (circleParabolicCurve T τ U r)
    rw [heval t,heval 0] at he
    refine he.trans (congrArg ((2*τ) * ·) ?_)
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (circle_parabolic_value_ae T τ U),
      ae_restrict_of_ae hG] with r hr hGr
    change q r = circleSobolevCoordinate T 4 0 (circleParabolicH4 T τ U r) at hr
    change G r = circleSobolevCoordinate T 4 4 (circleParabolicH4 T τ U r) at hGr
    exact finite_second_pairing_values T I (circleParabolicH4 T τ U r)
      (q r) (G r) (V r) hr hGr
  have hleft : Tendsto (fun I : Finset ℤ =>
      ‖circleFourierProjection T I (d t)‖^2-‖circleFourierProjection T I (d 0)‖^2)
      atTop (𝓝 (‖d t‖^2-‖d 0‖^2)) :=
    ((circle_fourier_projection_tendsto T (d t)).norm.pow 2).sub
      ((circle_fourier_projection_tendsto T (d 0)).norm.pow 2)
  have hright := (projected_inner_integral_tendsto T G V t).const_mul (2*τ)
  have he := tendsto_nhds_unique hleft
    (Filter.Tendsto.congr (fun I => (hfinite I).symm) hright)
  refine he.trans (congrArg ((2*τ) * ·) ?_)
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hG] with r hr
  exact congrArg (fun a : CircleL2 T => (inner ℂ a (V r)).re) hr

set_option maxHeartbeats 600000 in
/-- The principal H2 energy identity for every member of the actual
maximal-regularity space, independently of any PDE assumption. -/
theorem circle_parabolic_h2_energy_identity (U : CircleParabolicSpace T τ)
    (t : unitInterval) :
    (‖circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ U t)‖^2+
        4*‖circleSobolevCoordinate T 2 2 (circleParabolicCurve T τ U t)‖^2)-
      (‖circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ U 0)‖^2+
        4*‖circleSobolevCoordinate T 2 2 (circleParabolicCurve T τ U 0)‖^2) =
      (2*τ) * ∫ r in Iic t,
        (inner ℂ
          (circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ U r)+
            (4:ℂ) • circleSobolevCoordinate T 4 4 (circleParabolicH4 T τ U r))
          (circleParabolicTimeDerivative T τ U r)).re ∂volume := by
  let q : unitInterval → CircleL2 T :=
    fun r => circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ U r)
  let V : CircleTimeL2 T := circleParabolicTimeDerivative T τ U
  let G0 : CircleTimeL2 T := (circleSobolevCoordinate T 4 0).compLpL 2
    (volume : Measure unitInterval) (circleParabolicH4 T τ U)
  let G4 : CircleTimeL2 T := (circleSobolevCoordinate T 4 4).compLpL 2
    (volume : Measure unitInterval) (circleParabolicH4 T τ U)
  have hG0 := (circleSobolevCoordinate T 4 0).coeFn_compLpL
    (p := 2) (μ := (volume : Measure unitInterval)) (circleParabolicH4 T τ U)
  have hG4 := (circleSobolevCoordinate T 4 4).coeFn_compLpL
    (p := 2) (μ := (volume : Measure unitInterval)) (circleParabolicH4 T τ U)
  have hq : ∀ᵐ r ∂volume, q r = G0 r := by
    filter_upwards [circle_parabolic_value_ae T τ U,hG0] with r hr hGr
    exact hr.trans hGr.symm
  have hint0 : Integrable (fun r : unitInterval => (inner ℂ (q r) (V r)).re) volume := by
    apply ((RCLike.reCLM : ℂ →L[ℝ] ℝ).integrable_comp
      (L2.integrable_inner (𝕜 := ℂ) G0 V)).congr
    filter_upwards [hq] with r hr
    exact congrArg (fun a : CircleL2 T => (inner ℂ a (V r)).re) hr.symm
  have hint4 : Integrable (fun r : unitInterval =>
      (inner ℂ (circleSobolevCoordinate T 4 4 (circleParabolicH4 T τ U r)) (V r)).re)
      volume := by
    apply ((RCLike.reCLM : ℂ →L[ℝ] ℝ).integrable_comp
      (L2.integrable_inner (𝕜 := ℂ) G4 V)).congr
    filter_upwards [hG4] with r hr
    exact congrArg (fun a : CircleL2 T => (inner ℂ a (V r)).re) hr
  have hzero := unit_interval_primitive_norm_sq_energy τ q V
    (circle_parabolic_time_derivative_integrable T τ U)
    (circle_parabolic_integral_identity T τ U) t
  have hsecond := parabolic_second_energy T τ U t
  have hsplit :
      (∫ r in Iic t, (inner ℂ
        (q r+(4:ℂ) • circleSobolevCoordinate T 4 4 (circleParabolicH4 T τ U r))
        (V r)).re ∂volume) =
      (∫ r in Iic t, (inner ℂ (q r) (V r)).re ∂volume)+
        4*(∫ r in Iic t,
          (inner ℂ (circleSobolevCoordinate T 4 4 (circleParabolicH4 T τ U r))
            (V r)).re ∂volume) := by
    exact integral_re_inner_four q
      (fun r => circleSobolevCoordinate T 4 4 (circleParabolicH4 T τ U r)) V t hint0 hint4
  exact (combine_quadratic_energy hzero hsecond).trans
    (congrArg ((2*τ) * ·) hsplit.symm)

end Lemniscate
