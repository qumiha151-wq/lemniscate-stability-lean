import Lemniscate.ShortAdjointNormalization

/-! Geometric tails only through moment four. A coarse normalization lower
bound 1/2 is sufficient; no high-precision square root is used here. -/
namespace Lemniscate.CoarseArithmetic
open Finset

def shortRotationTailBound (k : Fin 3) : ℚ :=
  4*H*2^k.val*momentTail (k.val+2) qb 8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem short_rotation_tail_comparisons :
    (9/20:ℚ) < shortConstantInterval.lo ∧ shortFrequencyInterval.hi < (18/25:ℚ) ∧
    shortRotationTailBound 0 < (1/45000000:ℚ) ∧
    shortRotationTailBound 0+shortRotationTailBound 1 < (19/50000000:ℚ) ∧
    shortRotationTailBound 2 < (3/500000:ℚ) := by decide +kernel

theorem short_rotation_norm_gt_half : (1/2:ℝ) < shortRotationCoefficientNorm := by
  have hc := short_constant_fourier_enclosure.1
  have hr := short_frequency_enclosure.2
  have hcl := (Rat.cast_lt (K := ℝ)).mpr short_rotation_tail_comparisons.1
  have hru := (Rat.cast_lt (K := ℝ)).mpr short_rotation_tail_comparisons.2.1
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at hcl hru
  have hc0 : (9/20:ℝ) < constantCoefficient lemniscateFrequencySquared nome := hcl.trans_le hc
  have hr0 : 0 < lemniscateFrequencySquared := by
    have h := short_frequency_enclosure.1
    norm_num [shortFrequencyInterval] at h
    linarith
  have hr1 : lemniscateFrequencySquared < (18/25:ℝ) := hr.trans_lt hru
  have harg : 0 ≤ 2*constantCoefficient lemniscateFrequencySquared nome /
      (5*lemniscateFrequencySquared) := by positivity
  have hsq := Real.sq_sqrt harg
  have hn := Real.sqrt_nonneg (2*constantCoefficient lemniscateFrequencySquared nome /
    (5*lemniscateFrequencySquared))
  have hdiv : (1/4:ℝ) < 2*constantCoefficient lemniscateFrequencySquared nome /
      (5*lemniscateFrequencySquared) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    linarith
  unfold shortRotationCoefficientNorm
  nlinarith

theorem short_rotation_coefficient_majorant (j : ℕ) :
    0 ≤ shortRotationCoefficient j ∧ shortRotationCoefficient j ≤
      4*(H:ℝ)*((j+1:ℕ):ℝ)^2*(qb:ℝ)^(j+1) := by
  have hm := frequency_nome_coefficient_majorant (j+1) (by omega)
  simp only [fourierCoefficient,if_neg (by omega : j+1 ≠ 0)] at hm
  have hn := short_rotation_coefficient_norm_bounds.1
  have hi := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1/2)
    short_rotation_norm_gt_half.le
  norm_num at hi
  have hH : 0 ≤ (H:ℝ) := by norm_num [H,rhi,qb]
  have hq : 0 ≤ (qb:ℝ) := by norm_num [qb]
  have heven : 0 ≤ evenCoefficient lemniscateFrequencySquared nome (j+1) := hm.1
  constructor
  · unfold shortRotationCoefficient
    positivity
  · have hnum := mul_le_mul_of_nonneg_left hm.2
      (by positivity : (0:ℝ) ≤ 2*((j+1:ℕ):ℝ))
    have hprod := mul_le_mul hnum hi (inv_nonneg.mpr hn.le)
      (by positivity : (0:ℝ) ≤ 2*((j+1:ℕ):ℝ)*
        ((H:ℝ)*(((j+1:ℕ):ℝ)*(qb:ℝ)^(j+1))))
    unfold shortRotationCoefficient
    calc
      _ = (2*((j+1:ℕ):ℝ)*evenCoefficient lemniscateFrequencySquared nome (j+1))*
          shortRotationCoefficientNorm⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ _ := hprod
      _ = _ := by ring

theorem short_rotation_coefficient_tail (k : Fin 3) (N : ℕ) :
    Summable (fun n : ℕ => |shortRotationCoefficient (n+N)| *
      (2*((n+N+1:ℕ):ℝ))^k.val) ∧
    (∑' n : ℕ, |shortRotationCoefficient (n+N)| *
      (2*((n+N+1:ℕ):ℝ))^k.val) ≤
      4*(H:ℝ)*2^k.val*(momentTail (k.val+2) qb (N+1):ℝ) := by
  let majorant : ℕ → ℝ := fun n => 4*(H:ℝ)*2^k.val*
    (((n+(N+1):ℕ):ℝ)^(k.val+2)*(qb:ℝ)^(n+(N+1)))
  have hm (n : ℕ) : |shortRotationCoefficient (n+N)| *
      (2*((n+N+1:ℕ):ℝ))^k.val ≤ majorant n := by
    rw [abs_of_nonneg (short_rotation_coefficient_majorant _).1]
    have h := mul_le_mul_of_nonneg_right (short_rotation_coefficient_majorant (n+N)).2
      (by positivity : (0:ℝ) ≤ (2*((n+N+1:ℕ):ℝ))^k.val)
    refine h.trans_eq ?_
    dsimp only [majorant]
    rw [← Nat.add_assoc]
    simp only [mul_pow,pow_add]
    ring
  have hs := (moment_tail_sound (k.val+2) (by omega) qb
    (by norm_num [qb]) (N+1)).mul_left (4*(H:ℝ)*2^k.val)
  have ht := Summable.of_nonneg_of_le (fun n => by positivity) hm hs.summable
  refine ⟨ht, ?_⟩
  have h := ht.tsum_le_tsum hm hs.summable
  rw [hs.tsum_eq] at h
  exact h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem short_normalization_error_arithmetic :
    (1/45000000:ℚ)+(1/45000000:ℚ)^2 < (1/160000:ℚ)/250 ∧
    (19/50000000:ℚ)+5*(1/45000000:ℚ)^2 < (1/160000:ℚ)/16 ∧
    (3/500000:ℚ)+5*(1/45000000:ℚ)^2 < (1/160000:ℚ) ∧
    (1/1200000:ℚ)+shortTrialRationalCoeff 7+2*(2*(1/160000:ℚ)/250) <
      (1/200000:ℚ)/5 ∧
    (1/300000:ℚ)+17*shortTrialRationalCoeff 7+3*(2*(1/160000:ℚ)/250) <
      (1/200000:ℚ) := by decide +kernel

end Lemniscate.CoarseArithmetic
