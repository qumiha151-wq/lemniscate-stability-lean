import Lemniscate.OddSignedGeometry

/-! High-row entry estimates using the actual shifted frequency |n+alpha|,
with the sharper lower same-sign estimate needed by the paper's quartic. -/
namespace Lemniscate.OddArithmetic
open CoarseArithmetic

theorem odd_matrix_off_from_polynomial_bound (n m : ℤ) (hn : Odd n) (hm : Odd m)
    (hne : n ≠ m) (α B : ℝ) (hB : |oddEntryPolynomial n m α| ≤ 45*B) :
    |oddMatrixEntry α n m| ≤
      (45*(rhi:ℝ)*(H:ℝ))*(((n-m).natAbs/2:ℕ):ℝ)*(qb:ℝ)^((n-m).natAbs/2)*B := by
  let l := (n-m).natAbs/2
  have hl : 0 < l := odd_half_distance_pos n m hn hm hne
  have hc := theta_nome_coefficient_majorant l hl
  have hr : 0 ≤ thetaParameter :=
    (by norm_num [rlo] : (0:ℝ) ≤ (rlo:ℝ)).trans actual_nome_theta_r_bounds.1
  have hp : thetaParameter*fourierCoefficient thetaParameter nome l ≤
      (rhi:ℝ)*((H:ℝ)*((l:ℝ)*(qb:ℝ)^l)) :=
    mul_le_mul actual_nome_theta_r_bounds.2 hc.2 hc.1 (by norm_num [rhi])
  rw [oddMatrixEntry, if_neg hne, abs_mul, abs_mul, abs_of_nonneg hr, abs_of_nonneg hc.1]
  calc
    _ ≤ ((rhi:ℝ)*((H:ℝ)*((l:ℝ)*(qb:ℝ)^l)))*(45*B) :=
      mul_le_mul hp hB (abs_nonneg _) (by
        have hH : 0 ≤ (H:ℝ) := by norm_num [H, rhi, qb]
        have hq : 0 ≤ (qb:ℝ) := by norm_num [qb]
        have hrhi : 0 ≤ (rhi:ℝ) := by norm_num [rhi]
        positivity)
    _ = _ := by dsimp only [l]; ring

theorem odd_matrix_shifted_off_bound (n m : ℤ) (hn : Odd n) (hm : Odd m)
    (hne : n ≠ m) (α : ℝ) :
    |oddMatrixEntry α n m| ≤
      (45*(rhi:ℝ)*(H:ℝ))*(((n-m).natAbs/2:ℕ):ℝ)*(qb:ℝ)^((n-m).natAbs/2)*
        (|(n:ℝ)+α|^2+2*|(n:ℝ)+α| * (((n-m).natAbs/2:ℕ):ℝ)+
          (((n-m).natAbs/2:ℕ):ℝ)^2/3) := by
  apply odd_matrix_off_from_polynomial_bound n m hn hm hne α
  have hd : |((n:ℝ)+α)-((m:ℝ)+α)| = 2*(((n-m).natAbs/2:ℕ):ℝ) := by
    rw [show (n:ℝ)+α-((m:ℝ)+α) = (n:ℝ)-(m:ℝ) by ring]
    exact odd_half_distance_abs n m hn hm
  have hb := odd_real_polynomial_majorant ((n:ℝ)+α) ((m:ℝ)+α) |(n:ℝ)+α|
    (((n-m).natAbs/2:ℕ):ℝ) le_rfl (Nat.cast_nonneg _) hd
  simpa only [oddEntryPolynomial, add_sub_add_right_eq_sub] using hb

theorem odd_same_lower_entry_bound (s : ℤ) (hs : s = 1 ∨ s = -1) (j k : ℕ)
    (hk : k < j) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    |oddMatrixEntry α (oddSignedFrequency s j) (oddSignedFrequency s k)| ≤
      (45*(rhi:ℝ)*(H:ℝ))*((j-k:ℕ):ℝ)*(qb:ℝ)^(j-k)*|(oddSignedFrequency s j:ℝ)+α|^2 := by
  have hne := (odd_signed_frequency_injective s hs).ne (Ne.symm (Nat.ne_of_lt hk))
  have hfreq := (odd_signed_shift_bounds s hs j α hα hα').1
  have hlv : 2*((j-k:ℕ):ℝ) ≤ |(oddSignedFrequency s j:ℝ)+α| := by
    rw [Nat.cast_sub (le_of_lt hk)]
    have hkn := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hb := odd_lower_polynomial_bound |(oddSignedFrequency s j:ℝ)+α| ((j-k:ℕ):ℝ)
    (abs_nonneg _) (Nat.cast_nonneg _) hlv
  have hp : |oddEntryPolynomial (oddSignedFrequency s j) (oddSignedFrequency s k) α| ≤
      45*|(oddSignedFrequency s j:ℝ)+α|^2 := by
    rw [odd_lower_polynomial_identity s hs j k (le_of_lt hk) α hα hα', abs_mul,
      abs_of_pos (by norm_num : (0:ℝ) < 45)]
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have ht := odd_matrix_off_from_polynomial_bound _ _ (odd_signed_frequency_odd s hs j)
    (odd_signed_frequency_odd s hs k) hne α _ hp
  simpa only [odd_same_half_distance_lower s hs j k (le_of_lt hk)] using ht

theorem odd_same_upper_entry_bound (s : ℤ) (hs : s = 1 ∨ s = -1) (j k : ℕ)
    (hk : j < k) (α : ℝ) :
    |oddMatrixEntry α (oddSignedFrequency s j) (oddSignedFrequency s k)| ≤
      (45*(rhi:ℝ)*(H:ℝ))*((k-j:ℕ):ℝ)*(qb:ℝ)^(k-j)*
        (|(oddSignedFrequency s j:ℝ)+α|^2+
          2*|(oddSignedFrequency s j:ℝ)+α| * ((k-j:ℕ):ℝ)+((k-j:ℕ):ℝ)^2/3) := by
  have hne := (odd_signed_frequency_injective s hs).ne (Nat.ne_of_lt hk)
  have ht := odd_matrix_shifted_off_bound _ _ (odd_signed_frequency_odd s hs j)
    (odd_signed_frequency_odd s hs k) hne α
  simpa only [odd_same_half_distance_upper s hs j k (le_of_lt hk)] using ht

theorem odd_cross_entry_bound (s : ℤ) (hs : s = 1 ∨ s = -1) (j k : ℕ)
    (hj : 1 ≤ j) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    |oddMatrixEntry α (oddSignedFrequency s j) (oddSignedFrequency (-s) k)| ≤
      (45*(rhi:ℝ)*(H:ℝ))*(|(oddSignedFrequency s j:ℝ)+α|+(k:ℝ))*(qb:ℝ)^(j+k+1)*
        (2*|(oddSignedFrequency s j:ℝ)+α|+(k:ℝ))^2 := by
  have hsneg : -s = 1 ∨ -s = -1 := by rcases hs with rfl | rfl <;> norm_num
  have ht := odd_matrix_shifted_off_bound _ _ (odd_signed_frequency_odd s hs j)
    (odd_signed_frequency_odd (-s) hsneg k) (odd_cross_frequency_ne s hs j k) α
  rw [odd_cross_half_distance s hs j k] at ht
  let v : ℝ := |(oddSignedFrequency s j:ℝ)+α|
  let l : ℝ := ((j+k+1:ℕ):ℝ)
  have hv : 0 ≤ v := abs_nonneg _
  have hl : 0 ≤ l := Nat.cast_nonneg _
  have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg _
  have hvl : l ≤ v+(k:ℝ) := by
    have hb := (odd_signed_shift_bounds s hs j α hα hα').1
    have hjr : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
    dsimp only [l, v]
    push_cast
    linarith
  have hp : v^2+2*v*l+l^2/3 ≤ (2*v+(k:ℝ))^2 := by
    calc
      _ ≤ (v+l)^2 := by nlinarith [sq_nonneg l]
      _ ≤ _ := pow_le_pow_left₀ (add_nonneg hv hl) (by linarith) 2
  have hmul : l*(v^2+2*v*l+l^2/3) ≤ (v+(k:ℝ))*(2*v+(k:ℝ))^2 :=
    mul_le_mul hvl hp (by positivity) (by positivity)
  have hscalar : 0 ≤ (45*(rhi:ℝ)*(H:ℝ))*(qb:ℝ)^(j+k+1) := by
    have hH : 0 ≤ (H:ℝ) := by norm_num [H, rhi, qb]
    have hq : 0 ≤ (qb:ℝ) := by norm_num [qb]
    have hr : 0 ≤ (rhi:ℝ) := by norm_num [rhi]
    positivity
  calc
    _ ≤ (45*(rhi:ℝ)*(H:ℝ))*l*(qb:ℝ)^(j+k+1)*(v^2+2*v*l+l^2/3) := ht
    _ = ((45*(rhi:ℝ)*(H:ℝ))*(qb:ℝ)^(j+k+1))*(l*(v^2+2*v*l+l^2/3)) := by ring
    _ ≤ ((45*(rhi:ℝ)*(H:ℝ))*(qb:ℝ)^(j+k+1))*((v+(k:ℝ))*(2*v+(k:ℝ))^2) :=
      mul_le_mul_of_nonneg_left hmul hscalar
    _ = _ := by dsimp only [v]; ring

end Lemniscate.OddArithmetic
