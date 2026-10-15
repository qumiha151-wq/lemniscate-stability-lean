import Lemniscate.MatrixTailSeries

/-! The normalized cosine zero mode and symmetry complete the off-diagonal
entry bounds. Every statement concerns the explicit coefficient-defined matrix. -/
namespace Lemniscate.CoarseArithmetic

theorem cosine_zero_upper_tail (k : ℕ) (hk : 0 < k) :
    |cosineMatrixEntry thetaParameter nome 0 k| ≤
      (C:ℝ)*(k:ℝ)^2*(k:ℝ)*(qb:ℝ)^k := by
  have hr0 : 0 ≤ thetaParameter :=
    (by norm_num [rlo] : (0:ℝ) ≤ (rlo:ℝ)).trans actual_nome_theta_r_bounds.1
  have hc := theta_nome_coefficient_majorant k hk
  have hc0 : 0 ≤ fourierCoefficient thetaParameter nome k := hc.1
  have hroot : 15*Real.sqrt 2 ≤ (105:ℝ) := by
    have h := coarse_sqrt_two.2
    norm_num at h
    linarith
  have heq : cosineMatrixEntry thetaParameter nome 0 k =
      -((15*Real.sqrt 2)*(thetaParameter*fourierCoefficient thetaParameter nome k)*
        (k:ℝ)^2) := by
    simp [cosineMatrixEntry, Nat.ne_of_gt hk]
    ring
  calc
    _ = (15*Real.sqrt 2)*(thetaParameter*fourierCoefficient thetaParameter nome k)*
        (k:ℝ)^2 := by rw [heq, abs_neg, abs_of_nonneg (by positivity)]
    _ ≤ 105*((rhi:ℝ)*((H:ℝ)*((k:ℝ)*(qb:ℝ)^k)))*(k:ℝ)^2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hroot
          (mul_le_mul actual_nome_theta_r_bounds.2 hc.2 hc.1 (by norm_num [rhi]))
          (mul_nonneg hr0 hc.1) (by norm_num)) (sq_nonneg _)
    _ = _ := by simp only [C, Rat.cast_mul, Rat.cast_ofNat]; ring

theorem cosine_upper_tail_all (j k : ℕ) (hjk : j < k) :
    |cosineMatrixEntry thetaParameter nome j k| ≤
      (C:ℝ)*(2*(j:ℝ)+((k-j:ℕ):ℝ))^2*((k-j:ℕ):ℝ)*(qb:ℝ)^(k-j) := by
  by_cases hj : j = 0
  · subst j
    simpa using cosine_zero_upper_tail k hjk
  · exact cosine_upper_tail j k (Nat.pos_of_ne_zero hj) hjk

theorem cosine_matrix_symmetric (r q : ℝ) (j k : ℕ) :
    cosineMatrixEntry r q j k = cosineMatrixEntry r q k j := by
  by_cases hj : j = 0 <;> by_cases hk : k = 0 <;> by_cases h : j = k <;>
    simp [cosineMatrixEntry, hj, hk, h, eq_comm, Nat.add_comm] <;> ring_nf <;> simp

theorem cosine_lower_tail (j k : ℕ) (hkj : k < j) :
    |cosineMatrixEntry thetaParameter nome j k| ≤
      (C:ℝ)*(2*(j:ℝ))^2*((j-k:ℕ):ℝ)*(qb:ℝ)^(j-k) := by
  rw [cosine_matrix_symmetric thetaParameter nome j k]
  have hsq : (2*(k:ℝ)+((j-k:ℕ):ℝ))^2 ≤ (2*(j:ℝ))^2 := by
    apply pow_le_pow_left₀ (by positivity) _ 2
    rw [Nat.cast_sub hkj.le]
    have h : (k:ℝ) ≤ (j:ℝ) := by exact_mod_cast hkj.le
    linarith
  exact (cosine_upper_tail_all k j hkj).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq (by norm_num [C, H, rhi, qb]))
        (Nat.cast_nonneg _)) (pow_nonneg (by norm_num [qb]) _))

theorem cosine_tail_bound_all (j L : ℕ) (hL : 0 < L) :
    Summable (fun a : ℕ =>
      |cosineMatrixEntry thetaParameter nome j (j+(a+L))|) ∧
    (∑' a : ℕ, |cosineMatrixEntry thetaParameter nome j (j+(a+L))|) ≤
      (entryTailBound j L : ℝ) := by
  have hm (a : ℕ) :
      |cosineMatrixEntry thetaParameter nome j (j+(a+L))| ≤
      (C:ℝ)*(2*(j:ℝ)+((a+L:ℕ):ℝ))^2*((a+L:ℕ):ℝ)*(qb:ℝ)^(a+L) := by
    simpa only [Nat.add_sub_cancel_left] using
      cosine_upper_tail_all j (j+(a+L)) (by omega)
  have hs := Summable.of_nonneg_of_le (fun a => abs_nonneg _) hm
    (hasSum_entry_majorant j L).summable
  refine ⟨hs, ?_⟩
  simpa only [(hasSum_entry_majorant j L).tsum_eq] using
    hs.tsum_le_tsum hm (hasSum_entry_majorant j L).summable

end Lemniscate.CoarseArithmetic
