import Lemniscate.ShortAdjointApproximation
import Lemniscate.ShortAdjointNormData
import Lemniscate.ShortSineSobolevTail

/-! The exact interval comparisons are bounds for the actual H4 auxiliary
functions with the same common unit phase as the new matrix proof. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem short_actual_finite_vector_bounds :
    ‖(circleShortRotationApproximation T:CircleL2 T)‖ = 1 ∧
    inner ℂ (circleShortAdjointApproximation T:CircleL2 T)
      (circleShortRotationApproximation T:CircleL2 T) = 1 ∧
    shortVNorm T (circleShortRotationApproximation T) < 5 ∧
    ‖(circleShortAdjointApproximation T:CircleL2 T)‖ < 2 ∧
    shortH1Norm T (circleShortAdjointApproximation T) < 3 ∧
    ‖((circleShortAdjointApproximation T-circleShortRotationApproximation T:circleH4Domain T):
      CircleL2 T)‖ < (1/20:ℝ) ∧
    shortH1Norm T (circleShortAdjointApproximation T-circleShortRotationApproximation T) <
      (11/50:ℝ) := by
  let e : Fin 7 → ℝ := shortRotationSine shortActualCoefficient
  let p : Fin 7 → ℝ := shortAdjointSine shortActualCoefficient
  let z : Fin 7 → ℝ := fun i => p i-e i
  let E := circleSineTrialH4 T 7 (fun i => (e i:ℂ))
  let P := circleSineTrialH4 T 7 (fun i => (p i:ℂ))
  let Z := circleSineTrialH4 T 7 (fun i => (z i:ℂ))
  have hnE := short_sine_trial_norms_sq T (fun i => (e i:ℂ))
  have hnP := short_sine_trial_norms_sq T (fun i => (p i:ℂ))
  have hnZ := short_sine_trial_norms_sq T (fun i => (z i:ℂ))
  have hc := short_seven_norm_certificate
  have heV := short_seven_square_bound shortRotationSineInput e shortVWeight 25
    short_rotation_sine_input_sound hc.1
  have hp0 := short_seven_square_bound shortAdjointSineInput p (fun _ => 1) 4
    short_adjoint_sine_input_sound hc.2.1
  have hp1 := short_seven_square_bound shortAdjointSineInput p shortH1Weight 9
    short_adjoint_sine_input_sound hc.2.2.1
  have hz0 := short_seven_square_bound shortAdjointDifferenceInput z (fun _ => 1) ((1/20:ℚ)^2)
    short_adjoint_difference_input_sound hc.2.2.2.1
  have hz1 := short_seven_square_bound shortAdjointDifferenceInput z shortH1Weight ((11/50:ℚ)^2)
    short_adjoint_difference_input_sound hc.2.2.2.2.1
  have heV' : shortVNorm T E^2 < 25 := by
    rw [hnE.2.2]
    simpa [shortVWeight,Complex.norm_real,Real.norm_eq_abs,sq_abs] using heV
  have hp0' : ‖(P:CircleL2 T)‖^2 < 4 := by
    rw [hnP.1]
    simpa [Complex.norm_real,Real.norm_eq_abs,sq_abs] using hp0
  have hp1' : shortH1Norm T P^2 < 9 := by
    rw [hnP.2.1]
    simpa [shortH1Weight,Complex.norm_real,Real.norm_eq_abs,sq_abs] using hp1
  have hz0' : ‖(Z:CircleL2 T)‖^2 < (1/20:ℝ)^2 := by
    rw [hnZ.1]
    simpa [Complex.norm_real,Real.norm_eq_abs,sq_abs] using hz0
  have hz1' : shortH1Norm T Z^2 < (11/50:ℝ)^2 := by
    rw [hnZ.2.1]
    simpa [shortH1Weight,Complex.norm_real,Real.norm_eq_abs,sq_abs] using hz1
  let v : Fin 7 → ℝ := fun i => (i.val+1)*shortActualCoefficient (i.val+1)
  have hN : 0 < Real.sqrt (∑ i : Fin 7, v i^2) :=
    (by norm_num [shortRotationNormInput] : (0:ℝ) < (shortRotationNormInput.lo:ℝ)).trans_le
      short_rotation_norm_sound.1
  have hsumE : (∑ i : Fin 7, e i^2) = 1 := by
    change (∑ i : Fin 7, (v i/Real.sqrt (∑ j : Fin 7, v j^2))^2) = 1
    simp only [div_pow]
    rw [← Finset.sum_div,Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (v i)))]
    exact div_self (Real.sqrt_pos.mp hN).ne'
  have hsumP : (∑ i : Fin 7, p i*e i) = 1 := by
    let d : ℝ := ∑ i : Fin 7, shortAdjointTrialCoeff i.castSucc*e i
    have hd : d ≠ 0 := ne_of_gt
      ((by exact_mod_cast short_adjoint_pair_input_pos :
        (0:ℝ) < (shortAdjointPairInput.lo:ℝ)).trans_le short_adjoint_pair_input_sound.1)
    have hterm (i : Fin 7) : p i*e i = (shortAdjointTrialCoeff i.castSucc*e i)/d := by
      dsimp only [p,e,shortAdjointSine,d]
      ring
    simp only [hterm]
    rw [← Finset.sum_div]
    exact div_self hd
  have hEnorm : ‖(E:CircleL2 T)‖ = 1 := by
    have h := hnE.1
    simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs,hsumE] at h
    change ‖(E:CircleL2 T)‖^2 = 1 at h
    nlinarith only [h,norm_nonneg (E:CircleL2 T)]
  have hpair : inner ℂ (P:CircleL2 T) (E:CircleL2 T) = 1 := by
    rw [short_sine_trial_inner]
    simp only [Complex.conj_ofReal,← Complex.ofReal_mul,← Complex.ofReal_sum,hsumP]
    norm_num
  have heqE : circleShortRotationApproximation T = I • E := rfl
  have heqP : circleShortAdjointApproximation T = I • P := rfl
  have heqZ : circleShortAdjointApproximation T-circleShortRotationApproximation T = I • Z := by
    rw [heqE,heqP,← smul_sub]
    congr 1
    dsimp only [P,E,Z,z,circleSineTrialH4]
    simp only [Complex.ofReal_sub,sub_smul,Finset.sum_sub_distrib]
  rw [heqE,heqP]
  have hmass (f : circleH4Domain T) : ‖((I • f:circleH4Domain T):CircleL2 T)‖ =
      ‖(f:CircleL2 T)‖ := by
    change ‖I • (f:CircleL2 T)‖ = _
    rw [norm_smul,Complex.norm_I,one_mul]
  have hI : conj I * I = 1 := by simp
  refine ⟨by rw [hmass,hEnorm],?_,?_,?_,?_,?_,?_⟩
  · change inner ℂ (I • (P:CircleL2 T)) (I • (E:CircleL2 T)) = 1
    rw [inner_smul_left,inner_smul_right,← mul_assoc,hI,one_mul,hpair]
  · rw [short_v_norm_smul,Complex.norm_I,one_mul]
    nlinarith only [heV',short_v_norm_nonneg T E]
  · rw [hmass]
    nlinarith only [hp0',norm_nonneg (P:CircleL2 T)]
  · rw [short_h1_norm_smul,Complex.norm_I,one_mul]
    nlinarith only [hp1',short_h1_norm_nonneg T P]
  · rw [← heqP,← heqE,heqZ,hmass]
    nlinarith only [hz0',norm_nonneg (Z:CircleL2 T)]
  · rw [← heqP,← heqE,heqZ,short_h1_norm_smul,Complex.norm_I,one_mul]
    nlinarith only [hz1',short_h1_norm_nonneg T Z]

end Lemniscate
