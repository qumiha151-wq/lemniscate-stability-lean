import Lemniscate.PeriodicParabolicEquation
import Lemniscate.PeriodicFiniteParabolicSolution
import Lemniscate.PeriodicSobolevH4Jet
import Lemniscate.PeriodicH4Fourier
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Order.ProjIcc

/-! Uniqueness for the actual principal parabolic equation in the complete
time space. Fourier coefficients are first shown to satisfy their integral
equations using the recorded Bochner primitive and the almost-everywhere
PDE. A continuous scalar primitive then supplies its own classical
derivative, so no pointwise time derivative of the original solution is
assumed. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal Topology

private theorem unit_interval_volterra_eq_zero (y : C(unitInterval, ℂ)) (b : ℂ)
    (hy : ∀ t : unitInterval, y t = ∫ r in Iic t, b*y r ∂volume) :
    ∀ t : unitInterval, y t = 0 := by
  let clamp : ℝ → unitInterval := Set.projIcc (0:ℝ) 1 zero_le_one
  have hclamp (t : unitInterval) : clamp (t:ℝ) = t := Set.projIcc_val zero_le_one t
  let w : ℝ → ℂ := fun r => b*y (clamp r)
  have hw : Continuous w := continuous_const.mul (y.continuous.comp continuous_projIcc)
  let Y : ℝ → ℂ := fun t => ∫ r in (0:ℝ)..t, w r
  have hYderiv (t : ℝ) : HasDerivAt Y (w t) t :=
    intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable 0 t)
      hw.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt
  have hY (t : unitInterval) : Y (t:ℝ) = y t := by
    rw [show Y (t:ℝ) = ∫ r in Iic t, w (r:ℝ) ∂volume from
      (unit_interval_setIntegral w t).symm]
    simpa only [w,hclamp] using (hy t).symm
  have hODE (r : ℝ) (hr : r ∈ Ico (0:ℝ) 1) : w r = b*Y r := by
    let t : unitInterval := ⟨r,hr.1,hr.2.le⟩
    change b*y (clamp (t:ℝ)) = b*Y (t:ℝ)
    rw [hclamp,hY]
  have hzero : ∀ r ∈ Icc (0:ℝ) 1, Y r = 0 :=
    eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (f := Y) (f' := w) (K := ‖b‖)
      (continuous_iff_continuousAt.mpr (fun r => (hYderiv r).continuousAt)).continuousOn
      (fun r _ => (hYderiv r).hasDerivWithinAt)
      (by simp only [Y,intervalIntegral.integral_same])
      (fun r hr => by rw [hODE r hr,norm_mul])
  intro t
  exact (hY t).symm.trans (hzero (t:ℝ) t.property)

variable (T : ℝ) [Fact (0 < T)]

set_option maxHeartbeats 800000 in
/-- Zero initial data and zero principal forcing give the zero element of
the complete parabolic space. The proof uses the actual time L2 equation,
not a finite-mode or continuous-forcing hypothesis. -/
theorem circle_parabolic_principal_eq_zero (τ : ℝ) (U : CircleParabolicSpace T τ)
    (hinit : circleParabolicInitialValue T τ U = 0)
    (hPDE : circleParabolicPrincipalRHS T τ U = 0) : U = 0 := by
  let curve : C(unitInterval, CircleSobolevSpace T 2) := circleParabolicCurve T τ U
  let H : CircleTimeH4 T := circleParabolicH4 T τ U
  let v : CircleTimeL2 T := circleParabolicTimeDerivative T τ U
  let A₀ : CircleSobolevSpace T 4 →L[ℂ] CircleL2 T :=
    circleSobolevCoordinate T 4 0+(4:ℂ) • circleSobolevCoordinate T 4 4
  have hEq : v+(A₀.compLpL 2 (volume : Measure unitInterval)) H = 0 := hPDE
  have hEqAE : ∀ᵐ t : unitInterval ∂volume, v t+A₀ (H t) = 0 := by
    have hsum := Lp.coeFn_add v ((A₀.compLpL 2 (volume : Measure unitInterval)) H)
    have hA := A₀.coeFn_compLpL (p := 2) (μ := (volume : Measure unitInterval)) H
    filter_upwards [hsum,hA,Lp.coeFn_zero (CircleL2 T) 2
      (volume : Measure unitInterval)] with t ht hAt h0t
    have h := congrArg (fun f : CircleTimeL2 T => f t) hEq
    simpa only [ht,Pi.add_apply,hAt,h0t,Pi.zero_apply] using h
  have hcurve0 : curve 0 = 0 := hinit
  have hcoeffzero (n : ℤ) : ∀ t : unitInterval,
      fourierCoeff (circleSobolevCoordinate T 2 0 (curve t)) n = 0 := by
    let c : CircleL2 T →L[ℂ] ℂ := innerSL ℂ (fourierBasis (T := T) n)
    have hc (f : CircleL2 T) : c f = fourierCoeff f n := by
      change inner ℂ (fourierBasis (T := T) n) f = fourierCoeff f n
      rw [← HilbertBasis.repr_apply_apply,fourierBasis_repr]
    let y : C(unitInterval, ℂ) :=
      ⟨fun t => c (circleSobolevCoordinate T 2 0 (curve t)),
        c.continuous.comp ((circleSobolevCoordinate T 2 0).continuous.comp curve.continuous)⟩
    let rate : ℂ := 1+4*(circleFrequencyFactor T n)^4
    let b : ℂ := -(τ:ℂ)*rate
    have hfourth (f : CircleSobolevSpace T 4) :
        c (circleSobolevCoordinate T 4 4 f) =
          (circleFrequencyFactor T n)^4*c (circleSobolevCoordinate T 4 0 f) := by
      have h := circle_h4_fourth_fourier T (circleSobolevToH4Domain T f) n
      rw [circle_sobolev_h4_jet] at h
      simpa only [circle_sobolev_to_h4_domain_coe,hc] using h
    have hAcoeff (f : CircleSobolevSpace T 4) :
        c (A₀ f) = rate*c (circleSobolevCoordinate T 4 0 f) := by
      simp only [A₀,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
        map_add,map_smul,hfourth]
      dsimp only [rate]
      ring
    have hvcoeff : ∀ᵐ t : unitInterval ∂volume, c (v t) = -rate*y t := by
      filter_upwards [hEqAE,circle_parabolic_value_ae T τ U] with t ht hvalue
      have hval : c (circleSobolevCoordinate T 4 0 (H t)) = y t :=
        congrArg c hvalue.symm
      have h := congrArg c ht
      rw [map_add,map_zero,hAcoeff,hval] at h
      simpa only [neg_mul] using eq_neg_of_add_eq_zero_left h
    have hy0 : y 0 = 0 := by
      change c (circleSobolevCoordinate T 2 0 (curve 0)) = 0
      rw [hcurve0,map_zero,map_zero]
    have hy (t : unitInterval) : y t = ∫ r in Iic t, b*y r ∂volume := by
      have hprimitive :
          circleSobolevCoordinate T 2 0 (curve t)-circleSobolevCoordinate T 2 0 (curve 0) =
            τ • (∫ r in Iic t, v r ∂volume) :=
        circle_parabolic_integral_identity T τ U t
      have hid : y t-y 0 = τ • c (∫ r in Iic t, v r ∂volume) := by
        calc
          y t-y 0 = c (circleSobolevCoordinate T 2 0 (curve t)-
              circleSobolevCoordinate T 2 0 (curve 0)) := (c.map_sub _ _).symm
          _ = c (τ • (∫ r in Iic t, v r ∂volume)) := congrArg c hprimitive
          _ = τ • c (∫ r in Iic t, v r ∂volume) :=
            (c.restrictScalars ℝ).map_smul τ _
      have hvint : Integrable v ((volume : Measure unitInterval).restrict (Iic t)) :=
        (circle_parabolic_time_derivative_integrable T τ U).restrict
      have hcint : c (∫ r in Iic t, v r ∂volume) =
          ∫ r in Iic t, c (v r) ∂volume := (c.integral_comp_comm hvint).symm
      calc
        y t = y t-y 0 := by rw [hy0,sub_zero]
        _ = τ • c (∫ r in Iic t, v r ∂volume) := hid
        _ = τ • (∫ r in Iic t, c (v r) ∂volume) :=
          congrArg (fun z : ℂ => τ • z) hcint
        _ = τ • (∫ r in Iic t, -rate*y r ∂volume) :=
          congrArg (fun z : ℂ => τ • z)
            (integral_congr_ae (ae_restrict_of_ae hvcoeff))
        _ = ∫ r in Iic t, b*y r ∂volume := by
          rw [← integral_smul]
          apply integral_congr_ae
          exact Eventually.of_forall fun r => by
            change τ • (-rate*y r) = b*y r
            rw [real_smul]
            dsimp only [b]
            ring
    intro t
    have hyzero := unit_interval_volterra_eq_zero y b hy t
    change c (circleSobolevCoordinate T 2 0 (curve t)) = 0 at hyzero
    exact (hc (circleSobolevCoordinate T 2 0 (curve t))).symm.trans hyzero
  have hcurve : curve = 0 := by
    apply ContinuousMap.ext
    intro t
    apply circle_sobolev_value_injective T 2
    simp only [ContinuousMap.zero_apply,map_zero]
    apply circle_fourier_ext T
    intro n
    rw [circle_fourierCoeff_zero]
    exact hcoeffzero n t
  have hH : H = 0 := by
    apply Lp.ext
    filter_upwards [circle_parabolic_value_ae T τ U,
      Lp.coeFn_zero (CircleSobolevSpace T 4) 2 (volume : Measure unitInterval)] with t ht h0t
    rw [h0t,Pi.zero_apply]
    apply circle_sobolev_value_injective T 4
    rw [map_zero,← ht]
    change circleSobolevCoordinate T 2 0 (curve t) = 0
    rw [hcurve]
    simp only [ContinuousMap.zero_apply,map_zero]
  have hv : v = 0 := by
    simpa only [hH,map_zero,add_zero] using hEq
  apply Subtype.ext
  apply Prod.ext
  · exact hcurve
  · apply Prod.ext
    · exact hH
    · exact hv

end Lemniscate
