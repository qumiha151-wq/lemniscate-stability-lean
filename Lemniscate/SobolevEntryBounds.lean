import Lemniscate.CosineFiniteForm

/-! Polynomial weights for the H2 sequence form. These are distinct from the
decaying Schur weights used to prove dissipation. The entry bound below is a
summable distance kernel times the two H2 frequency weights. -/
namespace Lemniscate.CoarseArithmetic

noncomputable def frequencyWeight (j : ℕ) : ℝ := 1+(j:ℝ)^2

theorem frequencyWeight_pos (j : ℕ) : 0 < frequencyWeight j := by
  unfold frequencyWeight
  positivity

noncomputable def cosineKernel (l : ℕ) : ℝ :=
  if l = 0 then 512 else 2*(C:ℝ)*(l:ℝ)*(qb:ℝ)^l

theorem cosineKernel_nonneg (l : ℕ) : 0 ≤ cosineKernel l := by
  have hC : (0:ℝ) ≤ (C:ℝ) := by norm_num [C, H, rhi, qb]
  have hq : (0:ℝ) ≤ (qb:ℝ) := by norm_num [qb]
  unfold cosineKernel
  split_ifs <;> positivity

set_option maxRecDepth 100000 in
theorem coarse_h0_absolute_bound : absUpper (hInterval 0) ≤ 1 := by decide +kernel

theorem theta_nome_coefficient_absolute_bound (m : ℕ) :
    |fourierCoefficient thetaParameter nome m| ≤ 1 := by
  by_cases hm : m = 0
  · subst m
    exact (absUpper_sound _ _ (theta_nome_fourier_enclosure 0)).trans
      (by exact_mod_cast coarse_h0_absolute_bound)
  · have h := common_index_coefficient_majorant 1 m (by norm_num) (by omega)
    exact h.trans (by norm_num [H, rhi, qb])

theorem theta_times_coefficient_absolute_bound (m : ℕ) :
    |thetaParameter*fourierCoefficient thetaParameter nome m| ≤ 1 := by
  have hr0 : 0 ≤ thetaParameter :=
    (by norm_num [rlo] : (0:ℝ) ≤ (rlo:ℝ)).trans (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, thetaRLower]) (by norm_num [rhi, thetaRUpper])).1
  have hr1 : thetaParameter ≤ 1 := (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, thetaRLower]) (by norm_num [rhi, thetaRUpper])).2.trans (by norm_num [rhi])
  rw [abs_mul, abs_of_nonneg hr0]
  simpa only [one_mul] using mul_le_mul hr1 (theta_nome_coefficient_absolute_bound m)
    (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)

theorem cosine_diagonal_sobolev_bound (j : ℕ) :
    |cosineMatrixEntry thetaParameter nome j j| ≤ 512*(frequencyWeight j)^2 := by
  by_cases hj : j = 0
  · subst j
    norm_num [cosineMatrixEntry, frequencyWeight]
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
  have he : cosineMatrixEntry thetaParameter nome j j =
      -4*thetaParameter^2*(2*(j:ℝ))^4-42+
      45*thetaParameter*fourierCoefficient thetaParameter nome 0*(2*(j:ℝ))^2-
      60*thetaParameter*fourierCoefficient thetaParameter nome (j+j)*(2*(j:ℝ))^2 := by
    simp [cosineMatrixEntry, hj]
    ring
  rw [he]
  apply abs_le.mpr
  constructor <;> unfold frequencyWeight <;>
    nlinarith [sq_nonneg (j:ℝ), sq_nonneg ((j:ℝ)^2)]

theorem cosine_upper_sobolev_bound (j k : ℕ) (hjk : j < k) :
    |cosineMatrixEntry thetaParameter nome j k| ≤
      (2*(C:ℝ)*((k-j:ℕ):ℝ)*(qb:ℝ)^(k-j))*frequencyWeight j*frequencyWeight k := by
  have hC : (0:ℝ) ≤ (C:ℝ) := by norm_num [C, H, rhi, qb]
  have hq : (0:ℝ) ≤ (qb:ℝ) := by norm_num [qb]
  have he : 2*(j:ℝ)+((k-j:ℕ):ℝ) = (j:ℝ)+(k:ℝ) := by
    rw [Nat.cast_sub hjk.le]
    ring
  have hp : ((j:ℝ)+(k:ℝ))^2 ≤ 2*frequencyWeight j*frequencyWeight k := by
    unfold frequencyWeight
    nlinarith [sq_nonneg ((j:ℝ)-(k:ℝ)), mul_nonneg (sq_nonneg (j:ℝ)) (sq_nonneg (k:ℝ))]
  have h := cosine_upper_tail_all j k hjk
  rw [he] at h
  calc
    _ ≤ (C:ℝ)*((j:ℝ)+(k:ℝ))^2*((k-j:ℕ):ℝ)*(qb:ℝ)^(k-j) := h
    _ ≤ (C:ℝ)*(2*frequencyWeight j*frequencyWeight k)*((k-j:ℕ):ℝ)*(qb:ℝ)^(k-j) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) (Nat.cast_nonneg _))
        (pow_nonneg hq _)
    _ = _ := by ring

theorem cosine_sobolev_entry_bound (j k : ℕ) :
    |cosineMatrixEntry thetaParameter nome j k| ≤
      cosineKernel (j-k+(k-j))*frequencyWeight j*frequencyWeight k := by
  rcases lt_trichotomy j k with h | h | h
  · have hd : j-k+(k-j) = k-j := by omega
    rw [hd, cosineKernel, if_neg (Nat.ne_of_gt (Nat.sub_pos_of_lt h))]
    exact cosine_upper_sobolev_bound j k h
  · subst k
    simpa only [Nat.sub_self, zero_add, cosineKernel, if_pos rfl, ite_true, pow_two, mul_assoc] using
      cosine_diagonal_sobolev_bound j
  · have hd : j-k+(k-j) = j-k := by omega
    rw [hd, cosineKernel, if_neg (Nat.ne_of_gt (Nat.sub_pos_of_lt h)),
      cosine_matrix_symmetric thetaParameter nome j k]
    have hu := cosine_upper_sobolev_bound k j h
    convert! hu using 1 <;> ring

end Lemniscate.CoarseArithmetic
