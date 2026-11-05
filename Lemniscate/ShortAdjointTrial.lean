import Lemniscate.ShortAdjointNormalization
import Lemniscate.PeriodicMatrixIdentification
import Lemniscate.PeriodicSineAdjointTrial
import Lemniscate.PeriodicRotationNorm

/-! The new eight-mode coefficient residual is the residual of the genuine
circle formal adjoint.  No previous trial or finite Bloch certificate is
used in this identification. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem short_circle_sine_operator_entry (h : C(AddCircle T, ℂ)) (r q : ℝ)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient r q j:ℂ))
    (hr : (2*Real.pi/T)^2 = r) (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    circleBlochFourierEntry T h 0 (2*(i:ℤ)) (2*(j:ℤ))-
      circleBlochFourierEntry T h 0 (-(2*(i:ℤ))) (2*(j:ℤ)) =
        (shortSineOperatorEntry r q i j:ℂ) := by
  have hneg : -(2*(i:ℤ)) ≠ 2*(j:ℤ) := by omega
  have hpos : (2*(i:ℤ) = 2*(j:ℤ)) ↔ i = j := by omega
  have hfreq : -(2*(i:ℤ))-2*(j:ℤ) = -(2*(i:ℤ)+2*(j:ℤ)) := by ring
  have hr4 : (2*Real.pi/T)^4 = r^2 := by
    calc
      _ = ((2*Real.pi/T)^2)^2 := by ring
      _ = _ := by rw [hr]
  simp only [circleBlochFourierEntry,add_zero,if_neg hneg,hfreq,hs,
    circle_even_coefficient_difference T h r q hs hc,
    circle_even_coefficient_sum T h r q hc,hr,hr4,hpos,shortSineOperatorEntry]
  by_cases he : i = j
  · subst j
    simp only [if_pos rfl,Int.cast_neg,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]
    push_cast
    ring
  · simp only [if_neg he,Int.cast_neg,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]
    push_cast
    ring

noncomputable def circleShortAdjointTrial : circleH4Domain T :=
  circleSineTrialH4 T 8 (fun i => (shortAdjointTrialCoeff i:ℂ))

noncomputable def circleShortResidualSquare (f : CircleL2 T) : ℝ :=
  2 * ∑' j : ℕ, ‖fourierCoeff f (2*((j+1:ℕ):ℤ))‖^2 /
    (shortResidualWeight (j+1):ℝ)

theorem circle_short_adjoint_trial_residual_square
    (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared) :
    circleShortResidualSquare T (circleH4FormalAdjoint T h h₁ (circleShortAdjointTrial T)) <
      (1/200000:ℝ)^2 := by
  have hcoeff (k : ℕ) :
      fourierCoeff (circleH4FormalAdjoint T h h₁ (circleShortAdjointTrial T))
        (2*((k+1:ℕ):ℤ)) = evenSineFactor*(shortRawAdjointResidual (k+1):ℂ) := by
    rw [circleShortAdjointTrial,
      circle_adjoint_sine_trial_fourier T h h₁ h₂ hh hh₁ hreal h₁real h₂real]
    congr 1
    simp only [shortRawAdjointResidual,Complex.ofReal_sum,Complex.ofReal_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [← map_sub,short_circle_sine_operator_entry T h lemniscateFrequencySquared nome
      hs hc hr (j.val+1) (k+1) (by omega) (by omega),Complex.conj_ofReal]
    ring
  have hterm (k : ℕ) :
      ‖fourierCoeff (circleH4FormalAdjoint T h h₁ (circleShortAdjointTrial T))
        (2*((k+1:ℕ):ℤ))‖^2 / (shortResidualWeight (k+1):ℝ) =
      ‖evenSineFactor‖^2 * ((shortRawAdjointResidual (k+1))^2 /
        (shortResidualWeight (k+1):ℝ)) := by
    rw [hcoeff,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    ring
  have hn := congrArg norm evenSineFactor_normalization
  simp only [norm_mul,norm_conj,norm_one] at hn
  norm_num at hn
  have hn2 : 2*‖evenSineFactor‖^2 = 1 := by nlinarith only [hn]
  unfold circleShortResidualSquare
  simp only [hterm,tsum_mul_left,← mul_assoc,hn2,one_mul]
  exact short_raw_adjoint_residual_bound.2

theorem circle_short_residual_square_smul (c : ℂ) (f : CircleL2 T) :
    circleShortResidualSquare T (c • f) = ‖c‖^2 * circleShortResidualSquare T f := by
  unfold circleShortResidualSquare
  simp only [circle_fourierCoeff_smul,norm_mul,mul_pow,mul_div_assoc,tsum_mul_left]
  ring

theorem circle_short_normalized_residual_le (h h₁ : C(AddCircle T, ℂ))
    (e : CircleL2 T) (f : circleH4Domain T)
    (hp : 1 ≤ ‖inner ℂ (f:CircleL2 T) e‖)
    (hres : 0 ≤ circleShortResidualSquare T (circleH4FormalAdjoint T h h₁ f)) :
    circleShortResidualSquare T
      (circleH4FormalAdjoint T h h₁ (circleNormalizedTrial T e f)) ≤
      circleShortResidualSquare T (circleH4FormalAdjoint T h h₁ f) := by
  rw [circleNormalizedTrial,map_smul,circle_short_residual_square_smul,
    norm_inv,norm_conj]
  have hi : ‖inner ℂ (f:CircleL2 T) e‖⁻¹ ≤ (1:ℝ) := by
    exact inv_le_one_of_one_le₀ hp
  have hi0 : 0 ≤ ‖inner ℂ (f:CircleL2 T) e‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have hs := pow_le_pow_left₀ hi0 hi 2
  nlinarith

end Lemniscate
