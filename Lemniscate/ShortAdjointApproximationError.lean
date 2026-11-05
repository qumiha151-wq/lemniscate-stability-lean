import Lemniscate.ShortAdjointRotationError
import Lemniscate.ShortAdjointError

/-! The genuine adjoint is compared first with the new eight-mode trial,
then with the seven-mode vector used by the actual matrix compression. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem short_trial_head_split :
    circleShortAdjointTrial T =
      circleSineTrialH4 T 7 (fun i => (shortAdjointTrialCoeff i.castSucc:ℂ))+
        (shortAdjointTrialCoeff (Fin.last 7):ℂ) • circleSineH4 T 7 := by
  unfold circleShortAdjointTrial circleSineTrialH4
  rw [Fin.sum_univ_castSucc]
  rfl

theorem short_eighth_sine_h1 : shortH1Norm T (circleSineH4 T 7) < 17 := by
  have hd := circle_sine_h4_derivative_norm T ⟨0,by decide⟩ 7
  change ‖(circleH4Jet T (circleSineH4 T 7)).first‖ =
    (2*Real.pi/T*(2*(7+1:ℕ):ℝ))^1 at hd
  have hn : ‖(circleSineH4 T 7:CircleL2 T)‖ = 1 :=
    (circle_even_sine_orthonormal T).norm_eq_one 7
  have hκ := (short_angular_frequency_pos T).ne'
  have hs : shortH1Norm T (circleSineH4 T 7)^2 = 257 := by
    rw [short_h1_norm_sq,hn,hd]
    simp only [pow_one]
    change (1:ℝ)^2+(shortAngularFrequency T)⁻¹^2*
      (shortAngularFrequency T*(2*(7+1:ℕ):ℝ))^2 = _
    norm_num
    field_simp
    <;> ring
  nlinarith only [hs,short_h1_norm_nonneg T (circleSineH4 T 7)]

theorem short_raw_trial_l2_lt_two : ‖(circleShortAdjointTrial T:CircleL2 T)‖ < 2 := by
  have ht (i : Fin 8) : 0 < shortAdjointTrialCoeff i := by
    rw [← short_trial_rational_cast]
    exact_mod_cast short_trial_rational_positive.2.2 i
  calc
    _ ≤ ∑ i : Fin 8, ‖(shortAdjointTrialCoeff i:ℂ) • circleEvenSineMode T i.val‖ :=
      norm_sum_le _ _
    _ = ∑ i : Fin 8, shortAdjointTrialCoeff i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul,(circle_even_sine_orthonormal T).norm_eq_one,mul_one,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos (ht i)]
    _ < 2 := by
      norm_num [shortAdjointTrialCoeff,shortAdjointTrialNumerator,Fin.sum_univ_succ]

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)
include hq hp he hqreal hpreal hs hc ho hr

theorem short_actual_adjoint_approximation_error (ψ : circleH4Domain T)
    (hψnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p) = 1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (hψsector : InCircleEvenSineSector T (ψ:CircleL2 T)) :
    ‖((circleShortAdjointVector T ψ-circleShortAdjointApproximation T:
        circleH4Domain T):CircleL2 T)‖ < (1/200000:ℝ)/5 ∧
      shortH1Norm T (circleShortAdjointVector T ψ-circleShortAdjointApproximation T) <
        (1/200000:ℝ) := by
  let e := circleShortRotationVector T q p hq hp
  let E := circleShortRotationApproximation T
  let Ψ := circleShortAdjointVector T ψ
  let ΨN := circleShortAdjointApproximation T
  let P := shortTrialPairing
  let d := ∑ i : Fin 7, shortAdjointTrialCoeff i.castSucc*
    shortRotationSine shortActualCoefficient i
  let Φ7 := circleSineTrialH4 T 7 (fun i => (shortAdjointTrialCoeff i.castSucc:ℂ))
  let t := circleNormalizedTrial T (e:CircleL2 T) (circleShortAdjointTrial T)
  let g := (I/(P:ℂ)) • Φ7
  let b := shortAdjointTrialCoeff (Fin.last 7)
  have hP : 1 < P := short_trial_pairing_gt_one
  have hP0 : 0 < P := lt_trans (by norm_num) hP
  have hd : 0 < d :=
    (by exact_mod_cast short_adjoint_pair_input_pos :
      (0:ℝ) < (shortAdjointPairInput.lo:ℝ)).trans_le short_adjoint_pair_input_sound.1
  have hb : 0 ≤ b := by norm_num [b,shortAdjointTrialCoeff,shortAdjointTrialNumerator,Fin.last]
  have hpair0 := circle_short_trial_rotation_pairing T q p hq hp he hqreal hpreal hs hc hr
  have hpair : inner ℂ (circleShortAdjointTrial T:CircleL2 T) (e:CircleL2 T) = I*(P:ℂ) := by
    change inner ℂ (circleShortAdjointTrial T:CircleL2 T)
      ((-I) • circleUnitRotation T q p) = _
    rw [inner_smul_right]
    rw [inner_neg_right] at hpair0
    linear_combination I*hpair0
  have ht : t = (I/(P:ℂ)) • circleShortAdjointTrial T := by
    dsimp only [t,circleNormalizedTrial]
    rw [hpair]
    congr 1
    simp only [map_mul,Complex.conj_I,Complex.conj_ofReal]
    field_simp
    <;> simp only [Complex.I_sq]
    <;> ring
  have hnorm : inner ℂ (Ψ:CircleL2 T) ((-I) • circleUnitRotation T q p) = 1 := by
    change inner ℂ ((-I) • (ψ:CircleL2 T)) ((-I) • circleUnitRotation T q p) = 1
    rw [inner_smul_left,inner_smul_right,hψnorm]
    simp
  have hzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) Ψ = 0 := by
    change circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ((-I) • ψ) = 0
    rw [map_smul,hψzero,smul_zero]
  have hsector : InCircleEvenSineSector T (Ψ:CircleL2 T) :=
    circle_even_sine_sector_smul T (-I) _ hψsector
  have h8 := short_circle_adjoint_eight_mode_error T q p hq hp he hqreal hpreal hs hc ho hr
    (-I) (by simp) Ψ hnorm hzero hsector
  have htnorm : inner ℂ (t:CircleL2 T) (e:CircleL2 T) = 1 :=
    circle_normalized_trial_pairing T _ _ (by
      rw [hpair]
      exact mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hP0.ne'))
  have hscale : ‖I/(P:ℂ)‖ ≤ 1 := by
    rw [norm_div,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hP0]
    exact (div_le_one hP0).mpr hP.le
  have htmass : ‖(t:CircleL2 T)‖ ≤ 2 := by
    rw [ht]
    change ‖(I/(P:ℂ)) • (circleShortAdjointTrial T:CircleL2 T)‖ ≤ 2
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hscale).trans
      (short_raw_trial_l2_lt_two T).le
  have hsplit : t-g = (I/(P:ℂ)* (b:ℂ)) • circleSineH4 T 7 := by
    rw [ht,short_trial_head_split]
    dsimp only [g,Φ7,b]
    module
  have htail0 : ‖((t-g:circleH4Domain T):CircleL2 T)‖ ≤ b := by
    have hn : ‖(circleSineH4 T 7:CircleL2 T)‖ = 1 :=
      (circle_even_sine_orthonormal T).norm_eq_one 7
    rw [hsplit]
    change ‖(I/(P:ℂ)*(b:ℂ)) • (circleSineH4 T 7:CircleL2 T)‖ ≤ b
    rw [norm_smul,norm_mul,hn,mul_one,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb]
    exact mul_le_of_le_one_left hb hscale
  have htail1 : shortH1Norm T (t-g) ≤ 17*b := by
    rw [hsplit,short_h1_norm_smul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg hb]
    have h := mul_le_mul hscale (short_eighth_sine_h1 T).le
      (short_h1_norm_nonneg T _) (by norm_num : (0:ℝ) ≤ 1)
    nlinarith only [mul_le_mul_of_nonneg_right h hb]
  have hfinite := short_actual_finite_vector_bounds T
  have hgn : g = ((d/P:ℝ):ℂ) • ΨN := by
    dsimp only [g,ΨN,circleShortAdjointApproximation,Φ7,circleSineTrialH4]
    simp only [Finset.smul_sum,smul_smul,shortAdjointSine]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    change I/(P:ℂ)*(shortAdjointTrialCoeff i.castSucc:ℂ) =
      ((d/P:ℝ):ℂ)*(I*(shortAdjointTrialCoeff i.castSucc/d:ℝ))
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hd.ne',Complex.ofReal_ne_zero.mpr hP0.ne']
    <;> ring
  have hgpair : inner ℂ (g:CircleL2 T) (E:CircleL2 T) = ((d/P:ℝ):ℂ) := by
    rw [hgn]
    change inner ℂ (((d/P:ℝ):ℂ) • (ΨN:CircleL2 T)) (E:CircleL2 T) = _
    rw [inner_smul_left,Complex.conj_ofReal,hfinite.2.1,mul_one]
  have horth : inner ℂ ((t-g:circleH4Domain T):CircleL2 T) (E:CircleL2 T) = 0 := by
    rw [hsplit]
    change inner ℂ ((I/(P:ℂ)*(b:ℂ)) • circleEvenSineMode T 7)
      (I • ∑ i : Fin 7,
        (shortRotationSine shortActualCoefficient i:ℂ) • circleEvenSineMode T i.val) = 0
    rw [inner_smul_left,inner_smul_right,inner_sum]
    simp only [inner_smul_right]
    have hzero (i : Fin 7) : inner ℂ (circleEvenSineMode T 7)
        (circleEvenSineMode T i.val) = 0 := by
      rw [orthonormal_iff_ite.mp (circle_even_sine_orthonormal T),if_neg (by omega)]
    simp only [hzero,mul_zero,Finset.sum_const_zero]
  have hrot := short_actual_rotation_approximation_error T q p hq hp he hqreal hpreal hs hc ho hr
  have hdelta : |1-d/P| ≤ 2*((1/160000:ℝ)/250) := by
    have h := short_adjoint_truncated_pairing (t:CircleL2 T) (e:CircleL2 T)
      (E:CircleL2 T) (g:CircleL2 T) (d/P) htnorm horth hgpair
    exact h.trans (mul_le_mul htmass hrot.1.le (norm_nonneg _) (by norm_num))
  have h0 := short_adjoint_renormalization_error Ψ t g ΨN (d/P)
    (normSeminorm ℂ (circleH4Domain T)) (1/1200000) b 2 (2*((1/160000:ℝ)/250))
    hgn h8.1.le htail0 hfinite.2.2.2.1.le hdelta (by norm_num)
  have h1 := short_adjoint_renormalization_error Ψ t g ΨN (d/P)
    (shortH1Seminorm T) (1/300000) (17*b) 3 (2*((1/160000:ℝ)/250))
    hgn h8.2.1.le htail1 hfinite.2.2.2.2.1.le hdelta (by norm_num)
  have hc0 : (1/1200000:ℝ)+b+2*((1/160000:ℝ)/250)*2 < (1/200000:ℝ)/5 := by
    norm_num [b,shortAdjointTrialCoeff,shortAdjointTrialNumerator,Fin.last]
  have hc1 : (1/300000:ℝ)+17*b+2*((1/160000:ℝ)/250)*3 < (1/200000:ℝ) := by
    norm_num [b,shortAdjointTrialCoeff,shortAdjointTrialNumerator,Fin.last]
  exact ⟨h0.trans_lt hc0,h1.trans_lt hc1⟩

end Profile
end Lemniscate
