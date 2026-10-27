import Lemniscate.CosineLowRows
import Lemniscate.HighFrequency

/-! Entry and weight estimates needed to connect the high-frequency quartic
certificate to complete rows of the concrete coefficient-defined matrix. -/
namespace Lemniscate.CoarseArithmetic

theorem weight_global_bound (k : ℕ) : weight k ≤ weight 3*(a^k/a^3) := by
  by_cases hk : k < 3
  · have h : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases h with rfl | rfl | rfl <;> norm_num [weight, a]
  · exact le_of_eq (weight_large k (by omega))

theorem tailWeightFactor_eq_one (j : ℕ) (hj : 3 ≤ j) : tailWeightFactor j = 1 := by
  unfold tailWeightFactor
  rw [← weight_large j hj]
  exact div_self (ne_of_gt (weight_pos j))

theorem weight_ratio_lower (j k : ℕ) (hj : 3 ≤ j) (hkj : k ≤ j) :
    weight k/weight j ≤ 1/a^(j-k) := by
  have ha : a ≠ 0 := by norm_num [a]
  have hw : weight 3 ≠ 0 := ne_of_gt (weight_pos 3)
  have hp : a^j = a^k*a^(j-k) := by
    rw [← pow_add, Nat.add_sub_of_le hkj]
  calc
    _ ≤ (weight 3*(a^k/a^3))/weight j :=
      div_le_div_of_nonneg_right (weight_global_bound k) (le_of_lt (weight_pos j))
    _ = _ := by
      rw [weight_large j hj, hp]
      field_simp [ha, hw]

theorem cosine_weighted_lower_majorant (j k : ℕ) (hj : 3 ≤ j) (hkj : k < j) :
    cosineOffRow j k ≤
      (C:ℝ)*(2*(j:ℝ))^2*((j-k:ℕ):ℝ)*((qb/a:ℚ):ℝ)^(j-k) := by
  have hjw : (0:ℝ) < (weight j:ℝ) := by exact_mod_cast weight_pos j
  have hkw : (0:ℝ) < (weight k:ℝ) := by exact_mod_cast weight_pos k
  have hratio : (weight k:ℝ)/(weight j:ℝ) ≤ 1/(a:ℝ)^(j-k) := by
    exact_mod_cast weight_ratio_lower j k hj hkj.le
  have hC : (0:ℝ) ≤ (C:ℝ) := by norm_num [C, H, rhi, qb]
  have hqb : (0:ℝ) ≤ (qb:ℝ) := by norm_num [qb]
  simp only [cosineOffRow, if_neg (Nat.ne_of_lt hkj)]
  calc
    _ ≤ ((C:ℝ)*(2*(j:ℝ))^2*((j-k:ℕ):ℝ)*(qb:ℝ)^(j-k))*(1/(a:ℝ)^(j-k)) :=
      mul_le_mul (cosine_lower_tail j k hkj) hratio
        (le_of_lt (div_pos hkw hjw)) (by positivity)
    _ = _ := by simp only [Rat.cast_div, div_pow]; ring

set_option maxRecDepth 100000 in
theorem coarse_h0_le_one : hUpper 0 ≤ 1 := by decide +kernel

theorem cosine_diagonal_high_bound (j : ℕ) (hj : 0 < j) :
    cosineMatrixEntry thetaParameter nome j j ≤
      -4*(rlo:ℝ)^2*(2*(j:ℝ))^4+45*(rhi:ℝ)*(2*(j:ℝ))^2 := by
  have hr0 : 0 ≤ thetaParameter :=
    (by norm_num [rlo] : (0:ℝ) ≤ (rlo:ℝ)).trans (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, thetaRLower]) (by norm_num [rhi, thetaRUpper])).1
  have h0 : fourierCoefficient thetaParameter nome 0 ≤ 1 :=
    (theta_nome_fourier_enclosure 0).2.trans (by exact_mod_cast coarse_h0_le_one)
  have hsum : 0 ≤ fourierCoefficient thetaParameter nome (j+j) :=
    (theta_nome_coefficient_majorant (j+j) (by omega)).1
  have hp : thetaParameter*fourierCoefficient thetaParameter nome 0 ≤ (rhi:ℝ) := by
    calc
      _ ≤ thetaParameter*1 := mul_le_mul_of_nonneg_left h0 hr0
      _ = thetaParameter := mul_one _
      _ ≤ _ := (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, thetaRLower]) (by norm_num [rhi, thetaRUpper])).2
  have hsq : (rlo:ℝ)^2 ≤ thetaParameter^2 :=
    pow_le_pow_left₀ (by norm_num [rlo]) (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, thetaRLower]) (by norm_num [rhi, thetaRUpper])).1 2
  have h4 := mul_le_mul_of_nonneg_right hsq (by positivity : 0 ≤ (2*(j:ℝ))^4)
  have h2 := mul_le_mul_of_nonneg_right hp (sq_nonneg (2*(j:ℝ)))
  have hneg : 0 ≤ thetaParameter*fourierCoefficient thetaParameter nome (j+j)*(2*(j:ℝ))^2 :=
    mul_nonneg (mul_nonneg hr0 hsum) (sq_nonneg _)
  have he : cosineMatrixEntry thetaParameter nome j j =
      -4*thetaParameter^2*(2*(j:ℝ))^4-42+
      45*thetaParameter*fourierCoefficient thetaParameter nome 0*(2*(j:ℝ))^2-
      60*thetaParameter*fourierCoefficient thetaParameter nome (j+j)*(2*(j:ℝ))^2 := by
    simp [cosineMatrixEntry, Nat.ne_of_gt hj]
    ring
  rw [he]
  nlinarith

end Lemniscate.CoarseArithmetic
