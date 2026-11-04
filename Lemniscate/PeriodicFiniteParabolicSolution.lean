import Lemniscate.PeriodicParabolicSpace
import Lemniscate.PeriodicSobolevFourierPolynomial
import Lemniscate.PeriodicH2Fourier
import Lemniscate.LinearParabolicSolvability
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Actual finite Fourier solutions in the closed parabolic space.

The scalar solutions are the previously constructed integrating-factor
solutions. The unit-time primitive condition is proved using the actual
unit-interval volume measure and the fundamental theorem of calculus.
The stored velocity is the physical velocity, without a factor of tau.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology

theorem unit_interval_setIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ → E) (t : unitInterval) :
    (∫ r in Iic t, v (r : ℝ) ∂volume) = ∫ r in (0:ℝ)..(t:ℝ), v r := by
  have h := unitInterval.measurePreserving_coe.setIntegral_image_emb
    unitInterval.measurableEmbedding_coe v (Iic t)
  rw [image_subtype_val_Icc_Iic] at h
  have hsubset : Icc (0:ℝ) (t:ℝ) ⊆ Icc (0:ℝ) 1 :=
    fun _ hx => ⟨hx.1,hx.2.trans t.property.2⟩
  rw [Measure.restrict_restrict_of_subset hsubset] at h
  exact h.symm.trans ((integral_Icc_eq_integral_Ioc).trans
    (intervalIntegral.integral_of_le t.property.1).symm)

private theorem unit_interval_derivative_primitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (u v : ℝ → E) (τ : ℝ) (hv : Continuous v)
    (hd : ∀ r, HasDerivAt u (τ • v r) r) (t : unitInterval) :
    u (t:ℝ)-u 0 = τ • (∫ r in Iic t, v (r:ℝ) ∂volume) := by
  rw [unit_interval_setIntegral,← intervalIntegral.integral_smul]
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hd r) ((hv.const_smul τ).intervalIntegrable 0 (t:ℝ))).symm

variable (T : ℝ) [Fact (0 < T)]

local instance finiteParabolicSobolevSecondCountable (m : ℕ) :
    SecondCountableTopologyEither unitInterval (CircleSobolevSpace T m) where
  out := Or.inl (inferInstance : SecondCountableTopology unitInterval)

local instance finiteParabolicL2SecondCountable :
    SecondCountableTopologyEither unitInterval (CircleL2 T) where
  out := Or.inl (inferInstance : SecondCountableTopology unitInterval)

private theorem finite_sobolev_synthesis_coordinate (m : ℕ) (I : Finset ℤ)
    (a : I → ℂ) (j : Fin (m+1)) :
    circleSobolevCoordinate T m j (circleSobolevFourierSynthesis T m I a) =
      ∑ n : I, ((circleFrequencyFactor T n)^j.val*a n) • fourierBasis (T := T) (n:ℤ) := by
  simp only [circleSobolevFourierSynthesis,sum_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply,
    map_sum,map_smul,circle_sobolev_fourier_mode_coordinate,smul_smul]
  apply Finset.sum_congr rfl
  intro n _
  rw [mul_comm (a n)]

private theorem finite_parabolic_fourth_frequency (n : ℤ) :
    (circleFrequencyFactor T n)^4 = ((‖circleFrequencyFactor T n‖^4:ℝ):ℂ) := by
  calc
    (circleFrequencyFactor T n)^4 = ((circleFrequencyFactor T n)^2)^2 := by ring
    _ = (((-((2*Real.pi/T)^2*(n:ℝ)^2):ℝ):ℂ))^2 := by
      rw [circle_frequency_factor_sq]
    _ = ((‖circleFrequencyFactor T n‖^4:ℝ):ℂ) := by
      rw [show ‖circleFrequencyFactor T n‖^4 =
        (‖circleFrequencyFactor T n‖^2)^2 by ring,circle_frequency_factor_norm_sq]
      push_cast
      ring

/-- The prescribed continuous finite Fourier forcing in actual time L2. -/
def circleFiniteFourierTimeForcing (I : Finset ℤ) (G : I → ℝ → ℂ)
    (hG : ∀ n, Continuous (G n)) : CircleTimeL2 T :=
  ContinuousMap.toLp 2 (volume : Measure unitInterval) ℂ
    ⟨fun t => circleSobolevCoordinate T 4 0
      (circleSobolevFourierSynthesis T 4 I (fun n => G n (t:ℝ))),
      (circleSobolevCoordinate T 4 0).continuous.comp
        ((circleSobolevFourierSynthesis T 4 I).continuous.comp
          ((continuous_pi hG).comp continuous_subtype_val))⟩

set_option maxHeartbeats 800000 in
private theorem finite_parabolic_space_of_coefficients (τ : ℝ)
    (I : Finset ℤ) (c0 : I → ℂ) (G : I → ℝ → ℂ)
    (hG : ∀ n, Continuous (G n)) (u : I → ℝ → ℂ)
    (hinit : ∀ n, u n 0 = c0 n)
    (hd : ∀ n r, HasDerivAt (u n)
      (τ • (G n r-(1+4*‖circleFrequencyFactor T n‖^4) • u n r)) r) :
    let rate : I → ℝ := fun n => 1+4*‖circleFrequencyFactor T n‖^4
    let E : (I → ℂ) →L[ℂ] CircleL2 T :=
      (circleSobolevCoordinate T 4 0).comp (circleSobolevFourierSynthesis T 4 I)
    ∃ U : CircleParabolicSpace T τ,
      circleParabolicInitialValue T τ U = circleSobolevFourierSynthesis T 2 I c0 ∧
      (∀ t : unitInterval, circleParabolicCurve T τ U t =
        circleSobolevFourierSynthesis T 2 I (fun n => u n (t:ℝ))) ∧
      (∀ᵐ t : unitInterval ∂volume, circleParabolicH4 T τ U t =
        circleSobolevFourierSynthesis T 4 I (fun n => u n (t:ℝ))) ∧
      (∀ᵐ t : unitInterval ∂volume, circleParabolicTimeDerivative T τ U t =
        E (fun n => G n (t:ℝ)-rate n • u n (t:ℝ))) ∧
      circleParabolicTimeDerivative T τ U+
        ((circleSobolevCoordinate T 4 0+(4:ℂ) • circleSobolevCoordinate T 4 4).compLpL
          2 (volume : Measure unitInterval)) (circleParabolicH4 T τ U) =
        circleFiniteFourierTimeForcing T I G hG := by
  dsimp only
  let rate : I → ℝ := fun n => 1+4*‖circleFrequencyFactor T n‖^4
  let w : I → ℝ → ℂ := fun n r => G n r-rate n • u n r
  let E : (I → ℂ) →L[ℂ] CircleL2 T :=
    (circleSobolevCoordinate T 4 0).comp (circleSobolevFourierSynthesis T 4 I)
  let A0 : CircleSobolevSpace T 4 →L[ℂ] CircleL2 T :=
    circleSobolevCoordinate T 4 0+(4:ℂ) • circleSobolevCoordinate T 4 4
  have hu : ∀ n, Continuous (u n) := fun n =>
    continuous_iff_continuousAt.mpr fun r => (hd n r).continuousAt
  have hw : ∀ n, Continuous (w n) := fun n => (hG n).sub ((hu n).const_smul (rate n))
  have hUcontinuous : Continuous (fun r : ℝ => (fun n : I => u n r)) := continuous_pi hu
  have hWcontinuous : Continuous (fun r : ℝ => (fun n : I => w n r)) := continuous_pi hw
  let U2 : C(unitInterval,CircleSobolevSpace T 2) :=
    ⟨fun t => circleSobolevFourierSynthesis T 2 I (fun n => u n (t:ℝ)),
      (circleSobolevFourierSynthesis T 2 I).continuous.comp
        (hUcontinuous.comp continuous_subtype_val)⟩
  let U4 : C(unitInterval,CircleSobolevSpace T 4) :=
    ⟨fun t => circleSobolevFourierSynthesis T 4 I (fun n => u n (t:ℝ)),
      (circleSobolevFourierSynthesis T 4 I).continuous.comp
        (hUcontinuous.comp continuous_subtype_val)⟩
  let V : C(unitInterval,CircleL2 T) :=
    ⟨fun t => E (fun n => w n (t:ℝ)),
      E.continuous.comp (hWcontinuous.comp continuous_subtype_val)⟩
  let toH4 := ContinuousMap.toLp 2 (volume : Measure unitInterval) ℂ U4
  let toV := ContinuousMap.toLp 2 (volume : Measure unitInterval) ℂ V
  have hU4ae : (toH4 : unitInterval → CircleSobolevSpace T 4) =ᵐ[volume] U4 :=
    ContinuousMap.coeFn_toLp (p := 2) volume (𝕜 := ℂ) U4
  have hVae : (toV : unitInterval → CircleL2 T) =ᵐ[volume] V :=
    ContinuousMap.coeFn_toLp (p := 2) volume (𝕜 := ℂ) V
  have hvalue (b : I → ℂ) :
      circleSobolevCoordinate T 2 0 (circleSobolevFourierSynthesis T 2 I b) = E b := by
    change circleSobolevCoordinate T 2 0 (circleSobolevFourierSynthesis T 2 I b) =
      circleSobolevCoordinate T 4 0 (circleSobolevFourierSynthesis T 4 I b)
    rw [finite_sobolev_synthesis_coordinate,finite_sobolev_synthesis_coordinate]
    rfl
  have hcoeffderiv (r : ℝ) :
      HasDerivAt (fun s : ℝ => (fun n : I => u n s))
        (τ • (fun n : I => w n r)) r := by
    apply hasDerivAt_pi.mpr
    intro n
    exact hd n r
  have hvaluederiv (r : ℝ) :
      HasDerivAt (fun s : ℝ => E (fun n : I => u n s))
        (τ • E (fun n : I => w n r)) r := by
    have h := (E.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r (hcoeffderiv r)
    simpa only [map_smul,ContinuousLinearMap.coe_restrictScalars'] using! h
  let z : CircleParabolicAmbient T := (U2,(toH4,toV))
  have hz : z ∈ circleParabolicSubmodule T τ := by
    apply (circle_parabolic_mem_iff T τ z).mpr
    constructor
    · apply Lp.ext
      have h2 := (circleSobolevCoordinate T 2 0).coeFn_compLpL
        (p := 2) (μ := (volume : Measure unitInterval))
        (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℂ U2)
      have h2ae := ContinuousMap.coeFn_toLp (p := 2) volume (𝕜 := ℂ) U2
      have h4 := (circleSobolevCoordinate T 4 0).coeFn_compLpL
        (p := 2) (μ := (volume : Measure unitInterval)) toH4
      filter_upwards [h2,h2ae,h4,hU4ae] with t ht2 ht2ae ht4 ht4ae
      change ((circleSobolevCoordinate T 2 0).compLpL 2
        (volume : Measure unitInterval)
        (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℂ U2)) t =
        ((circleSobolevCoordinate T 4 0).compLpL 2
          (volume : Measure unitInterval) toH4) t
      rw [ht2,ht2ae,ht4,ht4ae]
      exact hvalue _
    · intro t
      change circleSobolevCoordinate T 2 0 (U2 t)-
        circleSobolevCoordinate T 2 0 (U2 0) = τ • (∫ r in Iic t, toV r ∂volume)
      have hi : (∫ r in Iic t, toV r ∂volume) = ∫ r in Iic t, V r ∂volume :=
        integral_congr_ae (ae_restrict_of_ae hVae)
      rw [hi]
      change circleSobolevCoordinate T 2 0
        (circleSobolevFourierSynthesis T 2 I (fun n => u n (t:ℝ)))-
        circleSobolevCoordinate T 2 0
          (circleSobolevFourierSynthesis T 2 I (fun n => u n 0)) = _
      rw [hvalue,hvalue]
      exact unit_interval_derivative_primitive
        (fun r => E (fun n : I => u n r)) (fun r => E (fun n : I => w n r)) τ
        (E.continuous.comp hWcontinuous) hvaluederiv t
  let U : CircleParabolicSpace T τ := ⟨z,hz⟩
  have hA0 (b : I → ℂ) : A0 (circleSobolevFourierSynthesis T 4 I b) =
      E (fun n => rate n • b n) := by
    simp only [A0,E,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply,finite_sobolev_synthesis_coordinate,
      Fin.val_zero,Fin.val_ofNat,pow_zero,one_mul,Finset.smul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [smul_smul,← add_smul]
    change (b n+(4:ℂ)*((circleFrequencyFactor T n)^4*b n)) •
        fourierBasis (T := T) (n:ℤ) =
      (rate n • b n) • fourierBasis (T := T) (n:ℤ)
    rw [finite_parabolic_fourth_frequency]
    congr 1
    dsimp only [rate]
    rw [real_smul]
    push_cast
    ring
  have hPDE : toV+(A0.compLpL 2 (volume : Measure unitInterval)) toH4 =
      circleFiniteFourierTimeForcing T I G hG := by
    apply Lp.ext
    have hsum := Lp.coeFn_add toV ((A0.compLpL 2 (volume : Measure unitInterval)) toH4)
    have hAp := A0.coeFn_compLpL (p := 2) (μ := (volume : Measure unitInterval)) toH4
    let forcing : C(unitInterval,CircleL2 T) :=
      ⟨fun t => E (fun n => G n (t:ℝ)),
        E.continuous.comp ((continuous_pi hG).comp continuous_subtype_val)⟩
    have hforcing : (circleFiniteFourierTimeForcing T I G hG : unitInterval → CircleL2 T)
        =ᵐ[volume] forcing :=
      ContinuousMap.coeFn_toLp (p := 2) volume (𝕜 := ℂ) forcing
    filter_upwards [hsum,hVae,hAp,hU4ae,hforcing] with t ht hv hp hu4 hf
    rw [ht,Pi.add_apply,hv,hp,hu4,hf]
    change E (fun n => w n (t:ℝ))+A0
      (circleSobolevFourierSynthesis T 4 I (fun n => u n (t:ℝ))) = E (fun n => G n (t:ℝ))
    rw [hA0,← map_add]
    congr 1
    funext n
    exact sub_add_cancel _ _
  refine ⟨U,?_,?_,?_,?_,?_⟩
  · change circleSobolevFourierSynthesis T 2 I (fun n => u n 0) = _
    congr 1
    funext n
    exact hinit n
  · intro t
    rfl
  · exact hU4ae
  · exact hVae
  · exact hPDE

set_option maxHeartbeats 800000 in
/-- The prescribed finite-mode equation has a genuine solution in the closed
parabolic space, with its actual coefficient derivatives and initial values. -/
theorem circle_finite_parabolic_solution (τ : ℝ) (hτ : 0 < τ)
    (I : Finset ℤ) (c0 : I → ℂ) (G : I → ℝ → ℂ)
    (hG : ∀ n, Continuous (G n)) :
    let rate : I → ℝ := fun n => 1+4*‖circleFrequencyFactor T n‖^4
    ∃ u : I → ℝ → ℂ,
    (∀ n, u n 0 = c0 n) ∧
    (∀ n r, HasDerivAt (u n) (τ • (G n r-rate n • u n r)) r) ∧
    let E : (I → ℂ) →L[ℂ] CircleL2 T :=
      (circleSobolevCoordinate T 4 0).comp (circleSobolevFourierSynthesis T 4 I)
    ∃ U : CircleParabolicSpace T τ,
      circleParabolicInitialValue T τ U = circleSobolevFourierSynthesis T 2 I c0 ∧
      (∀ t : unitInterval, circleParabolicCurve T τ U t =
        circleSobolevFourierSynthesis T 2 I (fun n => u n (t:ℝ))) ∧
      (∀ᵐ t : unitInterval ∂volume, circleParabolicH4 T τ U t =
        circleSobolevFourierSynthesis T 4 I (fun n => u n (t:ℝ))) ∧
      (∀ᵐ t : unitInterval ∂volume, circleParabolicTimeDerivative T τ U t =
        E (fun n => G n (t:ℝ)-rate n • u n (t:ℝ))) ∧
      circleParabolicTimeDerivative T τ U+
        ((circleSobolevCoordinate T 4 0+(4:ℂ) • circleSobolevCoordinate T 4 4).compLpL
          2 (volume : Measure unitInterval)) (circleParabolicH4 T τ U) =
        circleFiniteFourierTimeForcing T I G hG := by
  let rate : I → ℝ := fun n => 1+4*‖circleFrequencyFactor T n‖^4
  have hODE : ∃ u : I → ℝ → ℂ,
      (∀ n, u n 0 = c0 n) ∧
        ∀ n r, HasDerivAt (u n) (τ • (G n r-rate n • u n r)) r := by
    let a : I → ℝ := fun n => τ*rate n
    let Gτ : I → ℝ → ℂ := fun n r => τ • G n r
    let u : I → ℝ → ℂ := finiteModeParabolicSolution a c0 Gτ
    have ha : ∀ n, 0 < a n := by
      intro n
      dsimp only [a,rate]
      positivity
    have hGτ : ∀ n, Continuous (Gτ n) := fun n => (hG n).const_smul τ
    obtain ⟨hinit,hd,_⟩ := finite_mode_parabolic_solvability a ha c0 Gτ hGτ
    refine ⟨u,hinit,?_⟩
    intro n r
    simpa only [a,Gτ,smul_sub,smul_smul] using hd n r
  obtain ⟨u,hinit,hd⟩ := hODE
  exact ⟨u,hinit,hd,finite_parabolic_space_of_coefficients T τ I c0 G hG u hinit hd⟩

end Lemniscate
