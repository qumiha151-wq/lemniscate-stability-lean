import Lemniscate.VectorIntervalSoundness
import Lemniscate.VectorBoundsArithmetic

set_option maxHeartbeats 800000

/-! The certified intervals bound the actual normalized sine polynomials and
the complete H4 errors. No truncation error is assumed as a hypothesis. -/
namespace Lemniscate.CoarseArithmetic

theorem weighted_sum_interval_bound {N : ℕ} (offset : ℕ)
    (I : Fin N → Interval) (v : Fin N → ℝ) (hv : ∀ j, Contains (I j) (v j)) :
    (∑ j : Fin N, |v j| * ∑ k : Fin 5, (2*(offset+j.val+1:ℕ):ℝ)^k.val) ≤
      ((∑ j : Fin N, absUpper (I j) *
        ∑ k : Fin 5, (2*(offset+j.val+1:ℕ):ℚ)^k.val : ℚ):ℝ) := by
  push_cast
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (absUpper_sound _ _ (hv j))
    (Finset.sum_nonneg (fun k _ => by positivity))

theorem interval_l4_sound {N : ℕ} (I : Fin N → Interval) (v : Fin N → ℝ)
    (hv : ∀ j, Contains (I j) (v j)) :
    (∑ j : Fin N, |v j| * ∑ k : Fin 5, (2*(j.val+1:ℕ):ℝ)^k.val) ≤
      (intervalL4 I:ℝ) := by
  simpa only [Nat.zero_add,intervalL4] using weighted_sum_interval_bound 0 I v hv

theorem rescale_interval_bound (I : Interval) (x : ℝ) (hp : 0 < I.lo)
    (hx : Contains I x) :
    ‖1-(x:ℂ)⁻¹‖ ≤ (absUpper (add (reciprocalPositive I) (point (-1))):ℝ) := by
  have h := add_sound _ _ _ _ (reciprocalPositive_sound I x hp hx) (point_sound (-1))
  have hb := absUpper_sound _ _ h
  have heq : (1-(x:ℂ)⁻¹) = ((1-x⁻¹:ℝ):ℂ) := by push_cast; rfl
  rw [heq,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]
  simpa only [Rat.cast_neg,Rat.cast_one,one_div,sub_eq_add_neg] using hb

theorem rotation_error_expression_bound :
    (2*(H:ℝ)/rotationCoefficientNorm)*
        (∑ k : Fin 5, 2^k.val*(momentTail (k.val+2) qb 16:ℝ))+
      ‖1-(rotationFiniteNorm:ℂ)⁻¹‖ *
        (∑ j : Fin 15, |rotationSineCoefficient j.val| *
          ∑ k : Fin 5, (2*(j.val+1:ℕ):ℝ)^k.val) ≤ (rotationErrorUpper:ℝ) := by
  have hn : 0 < (rotationNormData.lo:ℝ) :=
    Rat.cast_pos.mpr vector_interval_certificate.norm_pos
  have hH : 0 ≤ (H:ℝ) := by norm_num [H,rhi,qb]
  have ht : 0 ≤ ∑ k : Fin 5, 2^k.val*(momentTail (k.val+2) qb 16:ℝ) := by
    apply Finset.sum_nonneg
    intro k _
    apply mul_nonneg (by positivity)
    have hs := moment_tail_sound (k.val+2) (by omega) qb (by norm_num [qb]) 16
    rw [← hs.tsum_eq]
    have hqb : 0 ≤ (qb:ℝ) := by norm_num [qb]
    exact tsum_nonneg (fun n => by positivity)
  have hdiv := div_le_div_of_nonneg_left (show 0 ≤ 2*(H:ℝ) by positivity) hn
    rotation_norm_data_sound.1
  have hp : 0 < rotationFiniteNormData.lo :=
    (by norm_num : (0:ℚ) < 999/1000).trans vector_interval_certificate.finite_norm_pos
  have hscale := rescale_interval_bound _ _ hp rotation_finite_norm_data_sound
  have hsum := interval_l4_sound
    (fun j : Fin 15 => rotationCoefficientData (Fin.castAdd 3 j))
    (fun j => rotationSineCoefficient j.val)
    (fun j => rotation_coefficient_data_sound (Fin.castAdd 3 j))
  have hsum0 : 0 ≤ ∑ j : Fin 15, |rotationSineCoefficient j.val| *
      ∑ k : Fin 5, (2*(j.val+1:ℕ):ℝ)^k.val := by positivity
  have hscale0 : 0 ≤ (absUpper rotationRescaleData:ℝ) := (norm_nonneg _).trans hscale
  have hmul := mul_le_mul hscale hsum hsum0 hscale0
  have h := add_le_add (mul_le_mul_of_nonneg_right hdiv ht) hmul
  simpa only [rotationErrorUpper,rotationRescaleData,Rat.cast_add,Rat.cast_mul,
    Rat.cast_div,Rat.cast_sum,Rat.cast_pow,Rat.cast_ofNat] using h

theorem adjoint_error_expression_bound :
    (∑ j : Fin 3, |adjointNormalizedCoefficient (Fin.natAdd 15 j)| *
        ∑ k : Fin 5, (2*(15+j.val+1:ℕ):ℝ)^k.val)+
      ‖1-(adjointFinitePairing:ℂ)⁻¹‖ *
        (∑ j : Fin 15, |adjointNormalizedCoefficient (Fin.castAdd 3 j)| *
          ∑ k : Fin 5, (2*(j.val+1:ℕ):ℝ)^k.val)+(27:ℝ)/10^14 ≤
      (adjointErrorUpper:ℝ) := by
  have htail := weighted_sum_interval_bound 15
    (fun j : Fin 3 => adjointCoefficientData (Fin.natAdd 15 j))
    (fun j => adjointNormalizedCoefficient (Fin.natAdd 15 j))
    (fun j => adjoint_coefficient_data_sound (Fin.natAdd 15 j))
  have hp : 0 < adjointFinitePairingData.lo :=
    (by norm_num : (0:ℚ) < 999/1000).trans vector_interval_certificate.finite_pair_pos
  have hscale := rescale_interval_bound _ _ hp adjoint_finite_pairing_data_sound
  have hsum := interval_l4_sound
    (fun j : Fin 15 => adjointCoefficientData (Fin.castAdd 3 j))
    (fun j => adjointNormalizedCoefficient (Fin.castAdd 3 j))
    (fun j => adjoint_coefficient_data_sound (Fin.castAdd 3 j))
  have hsum0 : 0 ≤ ∑ j : Fin 15, |adjointNormalizedCoefficient (Fin.castAdd 3 j)| *
      ∑ k : Fin 5, (2*(j.val+1:ℕ):ℝ)^k.val := by positivity
  have hscale0 : 0 ≤ (absUpper adjointRescaleData:ℝ) := (norm_nonneg _).trans hscale
  have hmul := mul_le_mul hscale hsum hsum0 hscale0
  have h := add_le_add_right (add_le_add htail hmul) ((27:ℝ)/10^14)
  simpa only [adjointErrorUpper,adjointRescaleData,Rat.cast_add,Rat.cast_mul,
    Rat.cast_div,Rat.cast_sum,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_natCast,
    add_comm,add_left_comm,add_assoc] using h

end Lemniscate.CoarseArithmetic
