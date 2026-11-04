import Lemniscate.PeriodicFiniteParabolicSolution
import Lemniscate.PeriodicParabolicWeights
import Lemniscate.PeriodicParabolicEstimates

/-! Maximal-regularity estimates for actual finite Fourier solutions.

The coefficients below are arbitrary genuine solutions of the scalar
equations. Consequently the estimate applies to differences of finite
approximations, without choosing an inverse or assuming its linearity.
The norm is the existing product norm of the closed parabolic space.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

local instance finiteEstimateTimeSecondCountable :
    SecondCountableTopologyEither unitInterval (CircleL2 T) where
  out := Or.inl (inferInstance : SecondCountableTopology unitInterval)

private theorem finite_synthesis_norm_sq (m : ℕ) (I : Finset ℤ) (a : I → ℂ) :
    ‖circleSobolevFourierSynthesis T m I a‖^2 =
      ∑ n : I, ‖a n‖^2*
        (∑ j : Fin (m+1), ‖circleFrequencyFactor T n‖^(2*j.val)) := by
  classical
  let c : ℤ → ℂ := fun n => if hn : n ∈ I then a ⟨n,hn⟩ else 0
  have h := circle_sobolev_fourier_polynomial_norm_sq T m I c
  rw [← circle_sobolev_fourier_synthesis_restrict T m I c,
    ← Finset.sum_coe_sort I (fun n : ℤ => ‖c n‖^2*
      ∑ j : Fin (m+1), ‖circleFrequencyFactor T n‖^(2*j.val))] at h
  simpa [c] using h

private theorem finite_synthesis_h2_norm_sq (I : Finset ℤ) (a : I → ℂ) :
    ‖circleSobolevFourierSynthesis T 2 I a‖^2 =
      ∑ n : I, (1+‖circleFrequencyFactor T n‖^2+
        ‖circleFrequencyFactor T n‖^4)*‖a n‖^2 := by
  rw [finite_synthesis_norm_sq]
  apply Finset.sum_congr rfl
  intro n _
  norm_num [Fin.sum_univ_succ,Fin.sum_univ_zero]
  ring

private theorem finite_synthesis_h4_norm_sq (I : Finset ℤ) (a : I → ℂ) :
    ‖circleSobolevFourierSynthesis T 4 I a‖^2 =
      ∑ n : I, (1+‖circleFrequencyFactor T n‖^2+
        ‖circleFrequencyFactor T n‖^4+‖circleFrequencyFactor T n‖^6+
        ‖circleFrequencyFactor T n‖^8)*‖a n‖^2 := by
  rw [finite_synthesis_norm_sq]
  apply Finset.sum_congr rfl
  intro n _
  norm_num [Fin.sum_univ_succ,Fin.sum_univ_zero]
  ring

private theorem finite_synthesis_value_norm_sq (I : Finset ℤ) (a : I → ℂ) :
    ‖circleSobolevCoordinate T 4 0 (circleSobolevFourierSynthesis T 4 I a)‖^2 =
      ∑ n : I, ‖a n‖^2 := by
  have hvalue : circleSobolevCoordinate T 4 0 (circleSobolevFourierSynthesis T 4 I a) =
      ∑ n : I, a n • fourierBasis (T := T) (n:ℤ) := by
    simp only [circleSobolevFourierSynthesis,sum_apply,
      ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply,
      map_sum,map_smul,circle_sobolev_fourier_mode_coordinate,Fin.val_zero,
      pow_zero,one_smul]
  have hb := (fourierBasis (T := T)).orthonormal.comp
    (fun n : I => (n:ℤ)) Subtype.val_injective
  have hsum := hb.inner_sum a a Finset.univ
  have hsum' : inner ℂ (∑ n : I, a n • fourierBasis (T := T) (n:ℤ))
      (∑ n : I, a n • fourierBasis (T := T) (n:ℤ)) =
        ∑ n : I, conj (a n)*a n := by
    simpa only [Function.comp_apply] using hsum
  rw [hvalue,norm_sq_eq_re_inner (𝕜 := ℂ),hsum']
  change (∑ n : I, conj (a n)*a n).re = ∑ n : I, ‖a n‖^2
  simp only [Complex.re_sum,Complex.conj_mul',← Complex.ofReal_pow,Complex.ofReal_re]

private theorem unit_interval_fullIntegral (f : ℝ → ℝ) :
    (∫ r in (0:ℝ)..1, f r) = ∫ r : unitInterval, f (r:ℝ) ∂volume := by
  have htop : Iic (1 : unitInterval) = univ := by
    ext r
    simp only [mem_Iic,mem_univ,iff_true]
    exact r.property.2
  simpa only [htop,Measure.restrict_univ,
    show ((1 : unitInterval) : ℝ) = 1 from rfl] using
    (unit_interval_setIntegral f (1 : unitInterval)).symm

set_option maxHeartbeats 1500000 in
/-- Any actual finite Fourier solution has the parabolic-space estimate
needed for Galerkin Cauchy convergence. The constant is uniform in the mode
set and remains bounded for zero initial data when `0 < tau ≤ 1`. -/
theorem circle_finite_parabolic_estimate
    (τ : ℝ) (hτ : 0 < τ) (I : Finset ℤ) (G : I → ℝ → ℂ)
    (hG : ∀ n, Continuous (G n)) (u : I → ℝ → ℂ)
    (hd : ∀ n r, HasDerivAt (u n)
      (τ • (G n r-(1+4*‖circleFrequencyFactor T n‖^4) • u n r)) r)
    (U : CircleParabolicSpace T τ)
    (hcurve : ∀ t : unitInterval, circleParabolicCurve T τ U t =
      circleSobolevFourierSynthesis T 2 I (fun n => u n (t:ℝ)))
    (hH4 : ∀ᵐ t : unitInterval ∂volume, circleParabolicH4 T τ U t =
      circleSobolevFourierSynthesis T 4 I (fun n => u n (t:ℝ)))
    (hvelocity : ∀ᵐ t : unitInterval ∂volume, circleParabolicTimeDerivative T τ U t =
      circleSobolevCoordinate T 4 0 (circleSobolevFourierSynthesis T 4 I
        (fun n => G n (t:ℝ)-(1+4*‖circleFrequencyFactor T n‖^4) • u n (t:ℝ)))) :
    ‖U‖^2 ≤ 40*((1+τ)*‖circleFiniteFourierTimeForcing T I G hG‖^2+
      (1+τ⁻¹)*‖circleParabolicInitialValue T τ U‖^2) := by
  let a : I → ℝ := fun n => 1+4*‖circleFrequencyFactor T n‖^4
  let W2 : I → ℝ := fun n => 1+‖circleFrequencyFactor T n‖^2+
    ‖circleFrequencyFactor T n‖^4
  let W4 : I → ℝ := fun n => 1+‖circleFrequencyFactor T n‖^2+
    ‖circleFrequencyFactor T n‖^4+‖circleFrequencyFactor T n‖^6+
    ‖circleFrequencyFactor T n‖^8
  let v : I → ℝ → ℂ := fun n r => G n r-a n • u n r
  let D : ℝ → ℝ := fun r => ∑ n : I, (‖v n r‖^2+W4 n*‖u n r‖^2)
  let EW : ℝ → ℝ := fun r => ∑ n : I, W2 n*‖u n r‖^2
  let forcing := circleFiniteFourierTimeForcing T I G hG
  let C := circleParabolicCurve T τ U
  let H := circleParabolicH4 T τ U
  let V := circleParabolicTimeDerivative T τ U
  let B : ℝ := 40*(τ*‖forcing‖^2+‖circleParabolicInitialValue T τ U‖^2)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hu (n : I) : Continuous (u n) :=
    continuous_iff_continuousAt.mpr fun r => (hd n r).continuousAt
  have hv (n : I) : Continuous (v n) := (hG n).sub ((hu n).const_smul (a n))
  have hVint : Integrable (fun t : unitInterval => ‖V t‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable V)).mp (Lp.memLp V)
  have hHint : Integrable (fun t : unitInterval => ‖H t‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable H)).mp (Lp.memLp H)
  have hDIntegral : (∫ r in (0:ℝ)..1, D r) = ‖V‖^2+‖H‖^2 := by
    rw [unit_interval_fullIntegral,unit_time_l2_norm_sq,unit_time_l2_norm_sq,
      ← integral_add hVint hHint]
    apply integral_congr_ae
    filter_upwards [hH4,hvelocity] with t htH htV
    change D (t:ℝ) = ‖circleParabolicTimeDerivative T τ U t‖^2+
      ‖circleParabolicH4 T τ U t‖^2
    rw [htV,htH,finite_synthesis_value_norm_sq,finite_synthesis_h4_norm_sq]
    simp only [D,W4,v,a,Finset.sum_add_distrib]
  have hforcing : (forcing : unitInterval → CircleL2 T) =ᵐ[volume]
      fun t => circleSobolevCoordinate T 4 0
        (circleSobolevFourierSynthesis T 4 I (fun n => G n (t:ℝ))) := by
    exact ContinuousMap.coeFn_toLp (p := 2) (volume : Measure unitInterval) (𝕜 := ℂ)
      ⟨fun t => circleSobolevCoordinate T 4 0
        (circleSobolevFourierSynthesis T 4 I (fun n => G n (t:ℝ))),
        (circleSobolevCoordinate T 4 0).continuous.comp
          ((circleSobolevFourierSynthesis T 4 I).continuous.comp
            ((continuous_pi hG).comp continuous_subtype_val))⟩
  have hFIntegral : (∫ r in (0:ℝ)..1, ∑ n : I, ‖v n r+a n • u n r‖^2) =
      ‖forcing‖^2 := by
    simp only [v,sub_add_cancel]
    rw [unit_interval_fullIntegral,unit_time_l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [hforcing] with t ht
    rw [ht,finite_synthesis_value_norm_sq]
  have hEWpoint (t : unitInterval) : EW (t:ℝ) = ‖C t‖^2 := by
    change EW (t:ℝ) = ‖circleParabolicCurve T τ U t‖^2
    rw [hcurve,finite_synthesis_h2_norm_sq]
  have hEWzero : EW 0 = ‖circleParabolicInitialValue T τ U‖^2 := by
    change EW 0 = ‖C (0 : unitInterval)‖^2
    simpa only [show ((0 : unitInterval) : ℝ) = 0 from rfl] using
      hEWpoint (0 : unitInterval)
  have henergy (t : unitInterval) : τ*(‖V‖^2+‖H‖^2)+‖C t‖^2 ≤ B := by
    have h := finite_mode_parabolic_sobolev_energy u v
      (fun n : I => ‖circleFrequencyFactor T n‖) (fun n => norm_nonneg _)
      τ 1 hτ zero_le_one hd hv (t:ℝ) t.property
    change τ*(∫ r in (0:ℝ)..1, D r)+EW (t:ℝ) ≤
      40*(τ*(∫ r in (0:ℝ)..1, ∑ n : I, ‖v n r+a n • u n r‖^2)+EW 0) at h
    rw [hDIntegral,hFIntegral,hEWpoint,hEWzero] at h
    exact h
  have hCpoint (t : unitInterval) : ‖C t‖^2 ≤ B := by
    exact (le_add_of_nonneg_left (by positivity : 0 ≤ τ*(‖V‖^2+‖H‖^2))).trans (henergy t)
  have hCnorm : ‖C‖^2 ≤ B := by
    have h : ‖C‖ ≤ Real.sqrt B := (C.norm_le (Real.sqrt_nonneg B)).mpr fun t => by
      apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg B)).mp
      simpa only [Real.sq_sqrt hB] using hCpoint t
    have hsq := (sq_le_sq₀ (norm_nonneg C) (Real.sqrt_nonneg B)).mpr h
    simpa only [Real.sq_sqrt hB] using hsq
  have hVτ : τ*‖V‖^2 ≤ B := by
    have h := henergy (0 : unitInterval)
    have hrem : 0 ≤ τ*‖H‖^2+‖C (0 : unitInterval)‖^2 := by positivity
    linear_combination h+hrem
  have hHτ : τ*‖H‖^2 ≤ B := by
    have h := henergy (0 : unitInterval)
    have hrem : 0 ≤ τ*‖V‖^2+‖C (0 : unitInterval)‖^2 := by positivity
    linear_combination h+hrem
  have hVnorm : ‖V‖^2 ≤ τ⁻¹*B := by
    have h := mul_le_mul_of_nonneg_left hVτ (inv_nonneg.mpr hτ.le)
    simpa only [← mul_assoc,inv_mul_cancel₀ (ne_of_gt hτ),one_mul] using h
  have hHnorm : ‖H‖^2 ≤ τ⁻¹*B := by
    have h := mul_le_mul_of_nonneg_left hHτ (inv_nonneg.mpr hτ.le)
    simpa only [← mul_assoc,inv_mul_cancel₀ (ne_of_gt hτ),one_mul] using h
  let R : ℝ := (1+τ⁻¹)*B
  have hBR : B ≤ R := by
    have hnonneg := mul_nonneg (inv_nonneg.mpr hτ.le) hB
    dsimp only [R]
    linear_combination hnonneg
  have hiBR : τ⁻¹*B ≤ R := by
    dsimp only [R]
    linear_combination hB
  have hUnorm : ‖U‖^2 ≤ R := by
    change (max ‖C‖ (max ‖H‖ ‖V‖))^2 ≤ R
    rcases le_total ‖C‖ (max ‖H‖ ‖V‖) with h | h
    · rw [max_eq_right h]
      rcases le_total ‖H‖ ‖V‖ with h' | h'
      · rw [max_eq_right h']
        exact hVnorm.trans hiBR
      · rw [max_eq_left h']
        exact hHnorm.trans hiBR
    · rw [max_eq_left h]
      exact hCnorm.trans hBR
  calc
    ‖U‖^2 ≤ R := hUnorm
    _ = 40*((1+τ)*‖circleFiniteFourierTimeForcing T I G hG‖^2+
        (1+τ⁻¹)*‖circleParabolicInitialValue T τ U‖^2) := by
      dsimp only [R,B,forcing]
      field_simp [ne_of_gt hτ]
      ring

end Lemniscate
