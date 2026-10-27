import Lemniscate.SineMatrix
import Lemniscate.GeometricMomentTails
import Lemniscate.CosineHighEntries

/-! High-frequency diagonal and lower-row bounds for the sine matrix. The
positive reflected-frequency diagonal correction is bounded explicitly. -/
namespace Lemniscate.CoarseArithmetic

theorem sine_lower_tail (j k : ℕ) (hkj : k < j) :
    |sineMatrixEntry thetaParameter nome j k| ≤
      (C:ℝ)*(2*(j:ℝ))^2*((j-k:ℕ):ℝ)*(qb:ℝ)^(j-k) := by
  rw [sine_matrix_symmetric thetaParameter nome j k]
  apply (sine_upper_tail k j hkj).trans
  have hC : (0:ℝ) ≤ (C:ℝ) := by norm_num [C, H, rhi, qb]
  have hq : (0:ℝ) ≤ (qb:ℝ) := by norm_num [qb]
  have hkj' : (k:ℝ) ≤ (j:ℝ) := by exact_mod_cast hkj.le
  have harg : 2*(k:ℝ)+((j-k:ℕ):ℝ) ≤ 2*(j:ℝ) := by
    rw [Nat.cast_sub hkj.le]
    linarith
  gcongr

theorem sine_diagonal_correction_bound (j : ℕ) (hj : 0 < j) :
    60*thetaParameter*fourierCoefficient thetaParameter nome (j+j)*(2*(j:ℝ))^2 ≤ 42 := by
  have hC : (0:ℝ) ≤ (H:ℝ) := by norm_num [H, rhi, qb]
  have hr : (0:ℝ) ≤ (rhi:ℝ) := by norm_num [rhi]
  have hq : (0:ℝ) ≤ (qb:ℝ) := by norm_num [qb]
  have hc := theta_nome_coefficient_majorant (j+j) (by omega)
  have hm : (j:ℝ)^3*((qb^2:ℚ):ℝ)^j ≤ (moment 3 (qb^2):ℝ) := by
    have hs := moment_sound 3 (by omega) (qb^2) (by norm_num [qb])
    simpa only [Finset.sum_singleton] using
      sum_le_hasSum ({j}:Finset ℕ) (fun k _ => by positivity) hs
  have hp := mul_le_mul (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, thetaRLower]) (by norm_num [rhi, thetaRUpper])).2 hc.2 hc.1 hr
  have hb := mul_le_mul_of_nonneg_right hp (sq_nonneg (2*(j:ℝ)))
  have hmain : 60*thetaParameter*fourierCoefficient thetaParameter nome (j+j)*(2*(j:ℝ))^2 ≤
      480*(rhi:ℝ)*(H:ℝ)*((j:ℝ)^3*((qb^2:ℚ):ℝ)^j) := by
    calc
      _ = 60*(thetaParameter*fourierCoefficient thetaParameter nome (j+j)*(2*(j:ℝ))^2) := by ring
      _ ≤ 60*((rhi:ℝ)*((H:ℝ)*(((j+j:ℕ):ℝ)*(qb:ℝ)^(j+j)))*(2*(j:ℝ))^2) :=
        mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = _ := by
        simp only [Nat.cast_add, Rat.cast_pow, pow_add]
        ring
  calc
    _ ≤ 480*(rhi:ℝ)*(H:ℝ)*((j:ℝ)^3*((qb^2:ℚ):ℝ)^j) := hmain
    _ ≤ 480*(rhi:ℝ)*(H:ℝ)*(moment 3 (qb^2):ℝ) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ ≤ 42 := by exact_mod_cast sine_diagonal_correction_certificate

theorem sine_diagonal_high_bound (j : ℕ) (hj : 0 < j) :
    sineMatrixEntry thetaParameter nome j j ≤
      -4*(rlo:ℝ)^2*(2*(j:ℝ))^4+45*(rhi:ℝ)*(2*(j:ℝ))^2 := by
  have hr0 : 0 ≤ thetaParameter :=
    (by norm_num [rlo] : (0:ℝ) ≤ (rlo:ℝ)).trans (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, thetaRLower]) (by norm_num [rhi, thetaRUpper])).1
  have h0 : fourierCoefficient thetaParameter nome 0 ≤ 1 :=
    (theta_nome_fourier_enclosure 0).2.trans (by exact_mod_cast coarse_h0_le_one)
  have hp : thetaParameter*fourierCoefficient thetaParameter nome 0 ≤ (rhi:ℝ) := by
    calc
      _ ≤ thetaParameter*1 := mul_le_mul_of_nonneg_left h0 hr0
      _ = thetaParameter := mul_one _
      _ ≤ _ := (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, thetaRLower]) (by norm_num [rhi, thetaRUpper])).2
  have hsq : (rlo:ℝ)^2 ≤ thetaParameter^2 :=
    pow_le_pow_left₀ (by norm_num [rlo]) (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, thetaRLower]) (by norm_num [rhi, thetaRUpper])).1 2
  have h4 := mul_le_mul_of_nonneg_right hsq (by positivity : 0 ≤ (2*(j:ℝ))^4)
  have h2 := mul_le_mul_of_nonneg_right hp (sq_nonneg (2*(j:ℝ)))
  have hc := sine_diagonal_correction_bound j hj
  have he : sineMatrixEntry thetaParameter nome j j =
      -4*thetaParameter^2*(2*(j:ℝ))^4-42+
      45*thetaParameter*fourierCoefficient thetaParameter nome 0*(2*(j:ℝ))^2+
      60*thetaParameter*fourierCoefficient thetaParameter nome (j+j)*(2*(j:ℝ))^2 := by
    simp only [sineMatrixEntry, ite_true, Nat.sub_self, Nat.zero_add]
    ring
  rw [he]
  nlinarith

end Lemniscate.CoarseArithmetic
