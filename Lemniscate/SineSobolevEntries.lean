import Lemniscate.SineFiniteForm
import Lemniscate.SobolevDissipation

/-! Absolute Sobolev bounds for the sine matrix and the shifted tail indices.
The same summable distance kernel controls both reflection signs. -/
namespace Lemniscate.CoarseArithmetic

theorem sine_diagonal_sobolev_bound (j : ℕ) :
    |sineMatrixEntry thetaParameter nome j j| ≤ 512*(frequencyWeight j)^2 := by
  have hr0 : 0 ≤ thetaParameter :=
    (by norm_num [rlo] : (0:ℝ) ≤ (rlo:ℝ)).trans (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, thetaRLower]) (by norm_num [rhi, thetaRUpper])).1
  have hr1 : thetaParameter ≤ 1 := (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, thetaRLower]) (by norm_num [rhi, thetaRUpper])).2.trans (by norm_num [rhi])
  have hrsq : thetaParameter^2 ≤ 1 := by nlinarith
  have hr4 := mul_le_mul_of_nonneg_right hrsq (by positivity : 0 ≤ (2*(j:ℝ))^4)
  have hr4pos : 0 ≤ thetaParameter^2*(2*(j:ℝ))^4 := by positivity
  have h0 := abs_le.mp (theta_times_coefficient_absolute_bound 0)
  have h2 := abs_le.mp (theta_times_coefficient_absolute_bound (j+j))
  have h0lo := mul_le_mul_of_nonneg_right h0.1 (sq_nonneg (2*(j:ℝ)))
  have h0hi := mul_le_mul_of_nonneg_right h0.2 (sq_nonneg (2*(j:ℝ)))
  have h2lo := mul_le_mul_of_nonneg_right h2.1 (sq_nonneg (2*(j:ℝ)))
  have h2hi := mul_le_mul_of_nonneg_right h2.2 (sq_nonneg (2*(j:ℝ)))
  have he : sineMatrixEntry thetaParameter nome j j =
      -4*thetaParameter^2*(2*(j:ℝ))^4-42+
      45*thetaParameter*fourierCoefficient thetaParameter nome 0*(2*(j:ℝ))^2+
      60*thetaParameter*fourierCoefficient thetaParameter nome (j+j)*(2*(j:ℝ))^2 := by
    simp only [sineMatrixEntry, ite_true, Nat.sub_self, Nat.zero_add]
    ring
  rw [he]
  apply abs_le.mpr
  constructor <;> unfold frequencyWeight <;>
    nlinarith [sq_nonneg (j:ℝ), sq_nonneg ((j:ℝ)^2)]

theorem sine_upper_sobolev_bound (j k : ℕ) (hjk : j < k) :
    |sineMatrixEntry thetaParameter nome j k| ≤
      (2*(C:ℝ)*((k-j:ℕ):ℝ)*(qb:ℝ)^(k-j))*frequencyWeight j*frequencyWeight k := by
  have hC : (0:ℝ) ≤ (C:ℝ) := by norm_num [C, H, rhi, qb]
  have hq : (0:ℝ) ≤ (qb:ℝ) := by norm_num [qb]
  have he : 2*(j:ℝ)+((k-j:ℕ):ℝ) = (j:ℝ)+(k:ℝ) := by
    rw [Nat.cast_sub hjk.le]
    ring
  have hp : ((j:ℝ)+(k:ℝ))^2 ≤ 2*frequencyWeight j*frequencyWeight k := by
    unfold frequencyWeight
    nlinarith [sq_nonneg ((j:ℝ)-(k:ℝ)), mul_nonneg (sq_nonneg (j:ℝ)) (sq_nonneg (k:ℝ))]
  have h := sine_upper_tail j k hjk
  rw [he] at h
  calc
    _ ≤ (C:ℝ)*((j:ℝ)+(k:ℝ))^2*((k-j:ℕ):ℝ)*(qb:ℝ)^(k-j) := h
    _ ≤ (C:ℝ)*(2*frequencyWeight j*frequencyWeight k)*((k-j:ℕ):ℝ)*(qb:ℝ)^(k-j) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) (Nat.cast_nonneg _))
        (pow_nonneg hq _)
    _ = _ := by ring

theorem sine_sobolev_entry_bound (j k : ℕ) :
    |sineMatrixEntry thetaParameter nome j k| ≤
      cosineKernel (j-k+(k-j))*frequencyWeight j*frequencyWeight k := by
  rcases lt_trichotomy j k with h | h | h
  · have hd : j-k+(k-j) = k-j := by omega
    rw [hd, cosineKernel, if_neg (Nat.ne_of_gt (Nat.sub_pos_of_lt h))]
    exact sine_upper_sobolev_bound j k h
  · subst k
    simpa only [Nat.sub_self, zero_add, cosineKernel, ite_true, pow_two, mul_assoc] using
      sine_diagonal_sobolev_bound j
  · have hd : j-k+(k-j) = j-k := by omega
    rw [hd, cosineKernel, if_neg (Nat.ne_of_gt (Nat.sub_pos_of_lt h)),
      sine_matrix_symmetric thetaParameter nome j k]
    have hu := sine_upper_sobolev_bound k j h
    convert! hu using 1
    ring

theorem sine_tail_sobolev_entry_bound (j k : ℕ) :
    |sineMatrixEntry thetaParameter nome (j+2) (k+2)| ≤
      cosineKernel (j-k+(k-j))*frequencyWeight (j+2)*frequencyWeight (k+2) := by
  simpa only [Nat.add_sub_add_right] using sine_sobolev_entry_bound (j+2) (k+2)

def HasSineTailH2Coefficients (v : ℕ → ℂ) : Prop :=
  Summable (fun j : ℕ => (frequencyWeight (j+2)*‖v j‖)^2)

theorem sine_tail_h2_iff (v : ℕ → ℂ) :
    HasSineTailH2Coefficients v ↔ HasH2Coefficients v := by
  constructor
  · intro hv
    apply Summable.of_nonneg_of_le (fun j => sq_nonneg _) _ hv
    intro j
    have hw : frequencyWeight j ≤ frequencyWeight (j+2) := by
      simp only [frequencyWeight, Nat.cast_add, Nat.cast_ofNat]
      nlinarith [Nat.cast_nonneg (α := ℝ) j]
    exact pow_le_pow_left₀ (mul_nonneg (frequencyWeight_pos j).le (norm_nonneg _))
      (mul_le_mul_of_nonneg_right hw (norm_nonneg _)) 2
  · intro hv
    apply Summable.of_nonneg_of_le (fun j => sq_nonneg _) _ (hv.mul_left 81)
    intro j
    have hw : frequencyWeight (j+2) ≤ 9*frequencyWeight j := by
      simp only [frequencyWeight, Nat.cast_add, Nat.cast_ofNat]
      nlinarith [sq_nonneg ((j:ℝ)-1)]
    have hs := pow_le_pow_left₀
      (mul_nonneg (frequencyWeight_pos (j+2)).le (norm_nonneg _))
      (mul_le_mul_of_nonneg_right hw (norm_nonneg (v j))) 2
    convert! hs using 1
    ring

end Lemniscate.CoarseArithmetic
