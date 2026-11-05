import Lemniscate.ShortSchurMatrices
import Lemniscate.ShortFourierEnclosure
import Lemniscate.IntervalMatrices

/-! Actual enclosures of the new seven-mode vectors.  The normalization is
recomputed from the new rational trial and the actual Fourier coefficients. -/
namespace Lemniscate.CoarseArithmetic
open Matrix Finset

noncomputable def shortActualCoefficient (j : ℕ) : ℝ :=
  fourierCoefficient lemniscateFrequencySquared nome j

def shortCoefficientInput (j : ℕ) : Interval :=
  if j=0 then shortConstantInterval else shortPositiveInterval j

theorem short_coefficient_input_sound (j : ℕ) :
    Contains (shortCoefficientInput j) (shortActualCoefficient j) := by
  by_cases hj : j=0
  · subst j
    simpa [shortCoefficientInput, shortActualCoefficient,
      fourierCoefficient] using short_constant_fourier_enclosure
  · simpa only [shortCoefficientInput, if_neg hj, shortActualCoefficient,
      fourierCoefficient, if_neg hj] using short_positive_fourier_enclosure j (by omega)

noncomputable def shortActualRotationRaw (j : Fin 7) : ℝ :=
  (j.val+1)*shortActualCoefficient (j.val+1)

def shortRotationRawInput (j : Fin 7) : Interval :=
  scale (shortCoefficientInput (j.val+1)) (j.val+1)

theorem short_rotation_raw_input_sound (j : Fin 7) :
    Contains (shortRotationRawInput j) (shortActualRotationRaw j) := by
  simpa only [shortRotationRawInput, shortActualRotationRaw, Rat.cast_natCast,
    Rat.cast_add, Rat.cast_one, Nat.cast_add, Nat.cast_one, mul_comm] using
    scale_sound _ _ (j.val+1) (short_coefficient_input_sound (j.val+1))

def shortRotationNormSqInput : Interval :=
  ⟨∑ i : Fin 7, (mul (shortRotationRawInput i) (shortRotationRawInput i)).lo,
   ∑ i : Fin 7, (mul (shortRotationRawInput i) (shortRotationRawInput i)).hi⟩

def shortRotationNormInput : Interval :=
  ⟨252313252163046453/10^18,252313252258517532/10^18⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem short_rotation_norm_certificate :
    0 ≤ shortRotationNormInput.lo ∧ 0 ≤ shortRotationNormInput.hi ∧
    shortRotationNormInput.lo^2 ≤ shortRotationNormSqInput.lo ∧
    shortRotationNormSqInput.hi ≤ shortRotationNormInput.hi^2 := by
  decide +kernel

theorem short_rotation_norm_sound : Contains shortRotationNormInput
    (Real.sqrt (∑ i : Fin 7, shortActualRotationRaw i ^ 2)) := by
  have hs : Contains shortRotationNormSqInput (∑ i : Fin 7, shortActualRotationRaw i ^ 2) := by
    simpa only [shortRotationNormSqInput, pow_two] using sum_interval_sound
      (fun i : Fin 7 => mul (shortRotationRawInput i) (shortRotationRawInput i))
      (fun i => shortActualRotationRaw i * shortActualRotationRaw i)
      (fun i => mul_sound _ _ _ _ (short_rotation_raw_input_sound i)
        (short_rotation_raw_input_sound i))
  exact sqrt_enclosure_sound _ _ _ _ hs short_rotation_norm_certificate.1
    short_rotation_norm_certificate.2.1 short_rotation_norm_certificate.2.2.1
    short_rotation_norm_certificate.2.2.2

def shortRotationSineInput (j : Fin 7) : Interval :=
  roundInterval 18 (dividePositive (shortRotationRawInput j) shortRotationNormInput)

theorem short_rotation_sine_input_sound (j : Fin 7) :
    Contains (shortRotationSineInput j) (shortRotationSine shortActualCoefficient j) := by
  apply roundInterval_sound
  exact dividePositive_sound _ _ _ _ (by norm_num [shortRotationNormInput])
    (short_rotation_raw_input_sound j) short_rotation_norm_sound

def shortTrialInput (j : Fin 8) : Interval := point (shortAdjointTrialNumerator j / 10^10)

theorem short_trial_input_sound (j : Fin 8) :
    Contains (shortTrialInput j) (shortAdjointTrialCoeff j) := by
  convert point_sound (shortAdjointTrialNumerator j / 10^10) using 1 <;>
    norm_num [shortTrialInput, shortAdjointTrialCoeff]

def shortAdjointPairInput : Interval :=
  ⟨∑ i : Fin 7, (mul (shortTrialInput i.castSucc) (shortRotationSineInput i)).lo,
   ∑ i : Fin 7, (mul (shortTrialInput i.castSucc) (shortRotationSineInput i)).hi⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem short_adjoint_pair_input_pos : 0 < shortAdjointPairInput.lo := by decide +kernel

theorem short_adjoint_pair_input_sound : Contains shortAdjointPairInput
    (∑ i : Fin 7, shortAdjointTrialCoeff i.castSucc * shortRotationSine shortActualCoefficient i) :=
  sum_interval_sound _ _ (fun i => mul_sound _ _ _ _ (short_trial_input_sound i.castSucc)
    (short_rotation_sine_input_sound i))

def shortAdjointSineInput (j : Fin 7) : Interval :=
  roundInterval 18 (dividePositive (shortTrialInput j.castSucc) shortAdjointPairInput)

theorem short_adjoint_sine_input_sound (j : Fin 7) :
    Contains (shortAdjointSineInput j) (shortAdjointSine shortActualCoefficient j) := by
  apply roundInterval_sound
  exact dividePositive_sound _ _ _ _ short_adjoint_pair_input_pos
    (short_trial_input_sound j.castSucc) short_adjoint_pair_input_sound

def shortSqrtTwoInput : Interval :=
  ⟨1414213562373095048/10^18,1414213562373095049/10^18⟩

theorem short_sqrt_two_input_sound : Contains shortSqrtTwoInput (Real.sqrt 2) := by
  apply sqrt_enclosure_sound (point 2) 2 _ _ (point_sound 2)
  all_goals norm_num [shortSqrtTwoInput, point]

def shortSineInput (v : Fin 7 → Interval) (i : Fin 15) : Interval :=
  if hi : i.val < 7 then scale (roundInterval 18
    (dividePositive (v ⟨6-i.val, by omega⟩) shortSqrtTwoInput)) (-1)
  else if hi : 7 < i.val then roundInterval 18
    (dividePositive (v ⟨i.val-8, by omega⟩) shortSqrtTwoInput)
  else point 0

theorem short_sine_input_sound (v : Fin 7 → Interval) (x : Fin 7 → ℝ)
    (hv : ∀ i, Contains (v i) (x i)) (i : Fin 15) :
    Contains (shortSineInput v i) (shortSineCoordinate x i) := by
  unfold shortSineInput shortSineCoordinate
  split_ifs with hi hj
  · simpa only [Rat.cast_neg, Rat.cast_one, mul_neg_one, neg_div] using
      scale_sound _ _ (-1) (roundInterval_sound 18 _ _
        (dividePositive_sound _ _ _ _ (by norm_num [shortSqrtTwoInput]) (hv _)
          short_sqrt_two_input_sound))
  · exact roundInterval_sound 18 _ _
      (dividePositive_sound _ _ _ _ (by norm_num [shortSqrtTwoInput]) (hv _)
        short_sqrt_two_input_sound)
  · simpa only [Rat.cast_zero] using point_sound 0

def shortRotationHeadInput : Fin 15 → Interval := shortSineInput shortRotationSineInput
def shortAdjointHeadInput : Fin 15 → Interval := shortSineInput shortAdjointSineInput
def shortAnchorHeadInput : Fin 15 → Interval :=
  shortSineInput (fun i => point (if i=0 then 1 else 0))

theorem short_rotation_head_input_sound (i : Fin 15) :
    Contains (shortRotationHeadInput i) (shortRotationHead shortActualCoefficient i) :=
  short_sine_input_sound _ _ short_rotation_sine_input_sound i

theorem short_adjoint_head_input_sound (i : Fin 15) :
    Contains (shortAdjointHeadInput i) (shortAdjointHead shortActualCoefficient i) :=
  short_sine_input_sound _ _ short_adjoint_sine_input_sound i

theorem short_anchor_head_input_sound (i : Fin 15) :
    Contains (shortAnchorHeadInput i) (shortAnchorHead i) := by
  apply short_sine_input_sound
  intro j
  by_cases hj : j=0
  · simpa only [if_pos hj, Rat.cast_one] using point_sound 1
  · simpa only [if_neg hj, Rat.cast_zero] using point_sound 0

end Lemniscate.CoarseArithmetic
