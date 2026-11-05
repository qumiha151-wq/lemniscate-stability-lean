import Lemniscate.ShortAdjointResidual

/-! A two-term analytic lower bound for the new trial pairing. The full
pairing is not evaluated to high precision, and normalization only decreases
the weighted residual. -/
namespace Lemniscate.CoarseArithmetic
open Finset

noncomputable def shortRotationCoefficientNorm : ℝ :=
  Real.sqrt (2*constantCoefficient lemniscateFrequencySquared nome /
    (5*lemniscateFrequencySquared))

noncomputable def shortRotationCoefficient (j : ℕ) : ℝ :=
  2*((j+1:ℕ):ℝ)*evenCoefficient lemniscateFrequencySquared nome (j+1) /
    shortRotationCoefficientNorm

noncomputable def shortTrialPairing : ℝ :=
  (∑ i : Fin 8, shortAdjointTrialCoeff i *
    (2*((i.val+1:ℕ):ℝ)*evenCoefficient lemniscateFrequencySquared nome (i.val+1))) /
      shortRotationCoefficientNorm

theorem short_rotation_coefficient_norm_bounds :
    0 < shortRotationCoefficientNorm ∧ shortRotationCoefficientNorm < (51/100:ℝ) := by
  have hr := short_frequency_enclosure
  have hc := short_constant_fourier_enclosure
  have hrat := short_pairing_coarse_comparisons
  have hrl : ((71/100:ℚ):ℝ) < (shortFrequencyInterval.lo:ℝ) := Rat.cast_lt.mpr hrat.1
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hrl
  have hr0 : (71/100:ℝ) < lemniscateFrequencySquared := hrl.trans_le hr.1
  have hc0 : 0 < constantCoefficient lemniscateFrequencySquared nome :=
    (by exact_mod_cast hrat.2.1 : (0:ℝ) < (shortConstantInterval.lo:ℝ)).trans_le hc.1
  have hhu : (shortConstantInterval.hi:ℝ) < ((23/50:ℚ):ℝ) := Rat.cast_lt.mpr hrat.2.2.1
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hhu
  have hcu : constantCoefficient lemniscateFrequencySquared nome < (23/50:ℝ) :=
    hc.2.trans_lt hhu
  have harg : 0 < 2*constantCoefficient lemniscateFrequencySquared nome /
      (5*lemniscateFrequencySquared) := by positivity
  have hupper : 2*constantCoefficient lemniscateFrequencySquared nome /
      (5*lemniscateFrequencySquared) ≤ 2*(23/50:ℝ)/(5*(71/100:ℝ)) := by
    exact div_le_div₀ (by positivity) (by linarith) (by norm_num) (by linarith)
  have hsq := Real.sq_sqrt harg.le
  have hn := Real.sqrt_nonneg (2*constantCoefficient lemniscateFrequencySquared nome /
    (5*lemniscateFrequencySquared))
  constructor
  · exact Real.sqrt_pos.mpr harg
  · dsimp only [shortRotationCoefficientNorm]
    nlinarith

/-- The first two positive terms already exceed the upper normalization
bound 51/100; the other six terms are merely nonnegative. -/
theorem short_trial_pairing_gt_one : 1 < shortTrialPairing := by
  have ht := short_trial_rational_positive
  have hrat := short_pairing_coarse_comparisons
  have h1 := (short_positive_fourier_enclosure 1 (by decide)).1
  have h2 := (short_positive_fourier_enclosure 2 (by decide)).1
  have hh1 : ((31/125:ℚ):ℝ) < ((shortPositiveInterval 1).lo:ℝ) :=
    Rat.cast_lt.mpr hrat.2.2.2.1
  have hh2 : ((21/1000:ℚ):ℝ) < ((shortPositiveInterval 2).lo:ℝ) :=
    Rat.cast_lt.mpr hrat.2.2.2.2
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh1 hh2
  have h1' : (31/125:ℝ) < evenCoefficient lemniscateFrequencySquared nome 1 :=
    hh1.trans_le h1
  have h2' : (21/1000:ℝ) < evenCoefficient lemniscateFrequencySquared nome 2 :=
    hh2.trans_le h2
  have ht0 : shortAdjointTrialCoeff 0 = 1 := by
    rw [← short_trial_rational_cast,ht.1]
    norm_num
  have ht1 : (1/5:ℝ) < shortAdjointTrialCoeff 1 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr ht.2.1
    norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
    simpa only [short_trial_rational_cast] using! h
  let f : Fin 8 → ℝ := fun i => shortAdjointTrialCoeff i *
    (2*((i.val+1:ℕ):ℝ)*evenCoefficient lemniscateFrequencySquared nome (i.val+1))
  have hf (i : Fin 8) : 0 ≤ f i := by
    have hti : 0 ≤ shortAdjointTrialCoeff i := by
      rw [← short_trial_rational_cast]
      exact_mod_cast (ht.2.2 i).le
    have hci : 0 ≤ evenCoefficient lemniscateFrequencySquared nome (i.val+1) := by
      simpa only [fourierCoefficient,if_neg (by omega : i.val+1 ≠ 0)] using
        (frequency_nome_coefficient_majorant (i.val+1) (by omega)).1
    dsimp only [f]
    positivity
  have htwo : f 0+f 1 ≤ ∑ i : Fin 8, f i := by
    have hs := sum_le_sum_of_subset_of_nonneg
      (subset_univ ({0,1}:Finset (Fin 8))) (fun i _ _ => hf i)
    simpa only [sum_pair (by decide : (0:Fin 8) ≠ 1)] using hs
  have hpair : (51/100:ℝ) < ∑ i : Fin 8, f i := by
    have hprod := mul_le_mul_of_nonneg_right ht1.le
      (by linarith : 0 ≤ evenCoefficient lemniscateFrequencySquared nome 2)
    have hsmall : f 0+f 1 = 2*evenCoefficient lemniscateFrequencySquared nome 1+
        4*shortAdjointTrialCoeff 1*evenCoefficient lemniscateFrequencySquared nome 2 := by
      dsimp only [f]
      rw [ht0]
      norm_num
      ring
    rw [hsmall] at htwo
    nlinarith only [hprod,h1',h2',htwo]
  unfold shortTrialPairing
  apply (lt_div_iff₀ short_rotation_coefficient_norm_bounds.1).mpr
  simpa only [one_mul] using short_rotation_coefficient_norm_bounds.2.trans hpair

end Lemniscate.CoarseArithmetic
