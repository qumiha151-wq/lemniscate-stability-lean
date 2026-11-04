import Lemniscate.PeriodicFiniteParabolicSolution
import Lemniscate.PeriodicSobolevFourierProjection
import Lemniscate.PeriodicTimeFourierProjection
import Lemniscate.PeriodicTimeApproximation
import Mathlib.Topology.Order.ProjIcc

/-! Common finite Fourier approximation of parabolic input data.

The initial value uses strong H2 Fourier convergence. Continuous time
forcing is first dense in time L2 and is then truncated spatially.
Intersecting the two eventual approximation conditions chooses the same
finite mode set directly. The coefficient functions are continuous on all
real times, by extending the continuous time curve with the interval clamp.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology

variable (T : ℝ) [Fact (0 < T)]

local instance parabolicDataTimeSecondCountable :
    SecondCountableTopologyEither unitInterval (CircleL2 T) where
  out := Or.inl (inferInstance : SecondCountableTopology unitInterval)

private theorem sobolev_projection_is_synthesis (m : ℕ) (I : Finset ℤ)
    (f : CircleSobolevSpace T m) :
    circleSobolevFourierSynthesis T m I
      (fun n => fourierCoeff (circleSobolevCoordinate T m 0 f) (n:ℤ)) =
        circleSobolevFourierProjection T m I f := by
  rw [circle_sobolev_fourier_synthesis_restrict]
  apply circle_sobolev_value_injective T m
  rw [circle_sobolev_fourier_polynomial_coordinate,
    circle_sobolev_fourier_projection_coordinate]
  simp only [Fin.val_zero,pow_zero,one_mul]

private theorem finite_time_projection_has_real_time_coefficients
    (H : C(unitInterval,CircleL2 T)) (I : Finset ℤ) :
    ∃ G : I → ℝ → ℂ, ∃ hG : ∀ n, Continuous (G n),
      circleFiniteFourierTimeForcing T I G hG =
        circleTimeFourierProjection T I
          (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℂ H) := by
  let clamp : ℝ → unitInterval := Set.projIcc (0:ℝ) 1 zero_le_one
  have hclamp : Continuous clamp := continuous_projIcc
  have hclamp_eq (t : unitInterval) : clamp (t:ℝ) = t :=
    Set.projIcc_val zero_le_one t
  let G : I → ℝ → ℂ := fun n r =>
    (innerSL ℂ (fourierBasis (T := T) (n:ℤ))) (H (clamp r))
  have hG (n : I) : Continuous (G n) :=
    (innerSL ℂ (fourierBasis (T := T) (n:ℤ))).continuous.comp
      (H.continuous.comp hclamp)
  have hcoeff (n : I) (t : unitInterval) :
      G n (t:ℝ) = fourierCoeff (H t) (n:ℤ) := by
    change inner ℂ (fourierBasis (T := T) (n:ℤ)) (H (clamp (t:ℝ))) = _
    rw [hclamp_eq,← fourierBasis_repr,HilbertBasis.repr_apply_apply]
  have hvalue (b : I → ℂ) :
      circleSobolevCoordinate T 4 0 (circleSobolevFourierSynthesis T 4 I b) =
        ∑ n : I, b n • fourierBasis (T := T) (n:ℤ) := by
    simp only [circleSobolevFourierSynthesis,sum_apply,
      ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply,
      map_sum,map_smul,circle_sobolev_fourier_mode_coordinate,Fin.val_zero,
      pow_zero,one_smul]
  refine ⟨G,hG,?_⟩
  let Hlp := ContinuousMap.toLp 2 (volume : Measure unitInterval) ℂ H
  have hH : (Hlp : unitInterval → CircleL2 T) =ᵐ[volume] H :=
    ContinuousMap.coeFn_toLp (p := 2) (volume : Measure unitInterval) (𝕜 := ℂ) H
  have hP := (circleFourierProjection T I).coeFn_compLpL
    (p := 2) (μ := (volume : Measure unitInterval)) Hlp
  have hfinite : (circleFiniteFourierTimeForcing T I G hG : unitInterval → CircleL2 T)
      =ᵐ[volume] fun t => circleSobolevCoordinate T 4 0
        (circleSobolevFourierSynthesis T 4 I (fun n => G n (t:ℝ))) :=
    ContinuousMap.coeFn_toLp (p := 2) (volume : Measure unitInterval) (𝕜 := ℂ)
      ⟨fun t => circleSobolevCoordinate T 4 0
        (circleSobolevFourierSynthesis T 4 I (fun n => G n (t:ℝ))),
        (circleSobolevCoordinate T 4 0).continuous.comp
          ((circleSobolevFourierSynthesis T 4 I).continuous.comp
            ((continuous_pi hG).comp continuous_subtype_val))⟩
  apply Lp.ext
  filter_upwards [hfinite,hP,hH] with t htF htP htH
  change (circleFiniteFourierTimeForcing T I G hG) t =
    ((circleFourierProjection T I).compLpL 2 (volume : Measure unitInterval) Hlp) t
  rw [htF,htP,htH,hvalue,circle_fourier_projection_apply]
  rw [← Finset.sum_coe_sort I (fun n : ℤ =>
    fourierCoeff (H t) n • fourierBasis (T := T) n)]
  apply Finset.sum_congr rfl
  intro n _
  rw [hcoeff]

set_option maxHeartbeats 800000 in
/-- Finite Fourier initial data and continuous finite Fourier forcing are
dense in the actual H2 times time-L2 data space, with one common mode set. -/
theorem circle_parabolic_finite_data_approximation
    (u0 : CircleSobolevSpace T 2) (F : CircleTimeL2 T) (ε : ℝ) (hε : 0 < ε) :
    ∃ I : Finset ℤ, ∃ c0 : I → ℂ, ∃ G : I → ℝ → ℂ,
      ∃ hG : ∀ n, Continuous (G n),
        max ‖circleSobolevFourierSynthesis T 2 I c0-u0‖
          ‖circleFiniteFourierTimeForcing T I G hG-F‖ < ε := by
  have hhalf : 0 < ε/2 := half_pos hε
  obtain ⟨H,hH⟩ := (circle_time_continuous_dense_range T).exists_dist_lt F hhalf
  rw [dist_comm,dist_eq_norm] at hH
  let Hlp := ContinuousMap.toLp 2 (volume : Measure unitInterval) ℂ H
  have hHnorm : ‖Hlp-F‖ < ε/2 := hH
  have hInitial : ∀ᶠ I : Finset ℤ in atTop,
      ‖circleSobolevFourierProjection T 2 I u0-u0‖ < ε := by
    have h := (circle_sobolev_fourier_projection_tendsto T 2 u0).eventually
      (Metric.ball_mem_nhds u0 hε)
    simpa only [Metric.mem_ball,dist_eq_norm] using h
  have hForcing : ∀ᶠ I : Finset ℤ in atTop,
      ‖circleTimeFourierProjection T I Hlp-Hlp‖ < ε/2 := by
    have h := (circle_time_fourier_projection_tendsto T Hlp).eventually
      (Metric.ball_mem_nhds Hlp hhalf)
    simpa only [Metric.mem_ball,dist_eq_norm] using h
  obtain ⟨I,hIinitial,hIforcing⟩ := (hInitial.and hForcing).exists
  let c0 : I → ℂ := fun n => fourierCoeff (circleSobolevCoordinate T 2 0 u0) (n:ℤ)
  obtain ⟨G,hG,hfinite⟩ := finite_time_projection_has_real_time_coefficients T H I
  refine ⟨I,c0,G,hG,max_lt_iff.mpr ⟨?_,?_⟩⟩
  · change ‖circleSobolevFourierSynthesis T 2 I
      (fun n => fourierCoeff (circleSobolevCoordinate T 2 0 u0) (n:ℤ))-u0‖ < ε
    rw [sobolev_projection_is_synthesis]
    exact hIinitial
  · rw [hfinite]
    change ‖circleTimeFourierProjection T I Hlp-F‖ < ε
    calc
      ‖circleTimeFourierProjection T I Hlp-F‖ ≤
          ‖circleTimeFourierProjection T I Hlp-Hlp‖+‖Hlp-F‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le
          (circleTimeFourierProjection T I Hlp-Hlp) (Hlp-F)
      _ < ε/2+ε/2 := add_lt_add hIforcing hHnorm
      _ = ε := by ring

end Lemniscate
