import Lemniscate.OddSignedEntries

/-! Normalized high-row entries: the lower and upper same-sign directions have
ratios qb/a and qb*a; opposite signs retain the exact qb*(qb/a)^j factor. -/
namespace Lemniscate.OddArithmetic
open CoarseArithmetic

noncomputable def oddSignedRow (α : ℝ) (s : ℤ) (j : ℕ) (t : ℤ) (k : ℕ) : ℝ :=
  oddWeightedOffEntry α (oddSignedFrequency s j) (oddSignedFrequency t k)/
    oddWeight (oddSignedFrequency s j) α

theorem odd_signed_row_nonneg (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2)
    (s t : ℤ) (j k : ℕ) : 0 ≤ oddSignedRow α s j t k := by
  unfold oddSignedRow oddWeightedOffEntry
  split_ifs
  · simp
  · exact div_nonneg (mul_nonneg (abs_nonneg _) (le_of_lt (odd_weight_positive _ α hα hα')))
      (le_of_lt (odd_weight_positive _ α hα hα'))

theorem odd_signed_row_diagonal (α : ℝ) (s : ℤ) (j : ℕ) : oddSignedRow α s j s j = 0 := by
  simp [oddSignedRow, oddWeightedOffEntry]

theorem odd_signed_row_off (α : ℝ) (s t : ℤ) (j k : ℕ)
    (hne : oddSignedFrequency s j ≠ oddSignedFrequency t k) :
    oddSignedRow α s j t k =
      |oddMatrixEntry α (oddSignedFrequency s j) (oddSignedFrequency t k)| *
        (oddWeight (oddSignedFrequency t k) α/oddWeight (oddSignedFrequency s j) α) := by
  simp only [oddSignedRow, oddWeightedOffEntry, if_neg (Ne.symm hne), mul_div_assoc]

theorem odd_lower_geometric_identity (j k : ℕ) (hk : k ≤ j) :
    (qb:ℝ)^(j-k)*(a:ℝ)^((k:ℤ)-(j:ℤ)) = ((qb/a:ℚ):ℝ)^(j-k) := by
  have he : (k:ℤ)-(j:ℤ) = -((j-k:ℕ):ℤ) := by omega
  rw [he, zpow_neg, zpow_natCast, Rat.cast_div, div_pow]
  rfl

theorem odd_upper_geometric_identity (j k : ℕ) (hk : j ≤ k) :
    (qb:ℝ)^(k-j)*(a:ℝ)^((k:ℤ)-(j:ℤ)) = ((qb*a:ℚ):ℝ)^(k-j) := by
  have he : (k:ℤ)-(j:ℤ) = ((k-j:ℕ):ℤ) := by omega
  rw [he, zpow_natCast, Rat.cast_mul, mul_pow]

theorem odd_cross_geometric_identity (j k : ℕ) :
    (qb:ℝ)^(j+k+1)*(a:ℝ)^((k:ℤ)-(j:ℤ)) =
      (qb:ℝ)*((qb/a:ℚ):ℝ)^j*((qb*a:ℚ):ℝ)^k := by
  have ha : (a:ℝ) ≠ 0 := by norm_num [a]
  rw [zpow_natCast_sub_natCast₀ ha]
  simp only [Rat.cast_div, Rat.cast_mul, pow_add, pow_one, div_pow, mul_pow]
  ring

theorem odd_same_lower_weighted_bound (s : ℤ) (hs : s = 1 ∨ s = -1) (j k : ℕ)
    (hj : 3 ≤ j) (hk : k < j) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    oddSignedRow α s j s k ≤
      (45*(rhi:ℝ)*(H:ℝ))*|(oddSignedFrequency s j:ℝ)+α|^2*
        ((j-k:ℕ):ℝ)*((qb/a:ℚ):ℝ)^(j-k) := by
  have hne := (odd_signed_frequency_injective s hs).ne (Ne.symm (Nat.ne_of_lt hk))
  rw [odd_signed_row_off α s s j k hne]
  have he := odd_same_lower_entry_bound s hs j k hk α hα hα'
  have hw := odd_same_branch_weight_ratio s hs j k hj α hα hα'
  have hH : 0 ≤ (H:ℝ) := by norm_num [H, rhi, qb]
  have hq : 0 ≤ (qb:ℝ) := by norm_num [qb]
  have hr : 0 ≤ (rhi:ℝ) := by norm_num [rhi]
  have hb := mul_le_mul he hw
    (le_of_lt (div_pos (odd_weight_positive _ α hα hα') (odd_weight_positive _ α hα hα')))
    (by positivity)
  refine hb.trans_eq ?_
  calc
    _ = ((45*(rhi:ℝ)*(H:ℝ))*|(oddSignedFrequency s j:ℝ)+α|^2*((j-k:ℕ):ℝ))*
        ((qb:ℝ)^(j-k)*(a:ℝ)^((k:ℤ)-(j:ℤ))) := by ring
    _ = _ := by rw [odd_lower_geometric_identity j k (le_of_lt hk)]

theorem odd_same_upper_weighted_bound (s : ℤ) (hs : s = 1 ∨ s = -1) (j k : ℕ)
    (hj : 3 ≤ j) (hk : j < k) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    oddSignedRow α s j s k ≤
      (45*(rhi:ℝ)*(H:ℝ))*((k-j:ℕ):ℝ)*((qb*a:ℚ):ℝ)^(k-j)*
        (|(oddSignedFrequency s j:ℝ)+α|^2+2*|(oddSignedFrequency s j:ℝ)+α| *
          ((k-j:ℕ):ℝ)+((k-j:ℕ):ℝ)^2/3) := by
  have hne := (odd_signed_frequency_injective s hs).ne (Nat.ne_of_lt hk)
  rw [odd_signed_row_off α s s j k hne]
  have he := odd_same_upper_entry_bound s hs j k hk α
  have hw := odd_same_branch_weight_ratio s hs j k hj α hα hα'
  have hH : 0 ≤ (H:ℝ) := by norm_num [H, rhi, qb]
  have hq : 0 ≤ (qb:ℝ) := by norm_num [qb]
  have hr : 0 ≤ (rhi:ℝ) := by norm_num [rhi]
  have hb := mul_le_mul he hw
    (le_of_lt (div_pos (odd_weight_positive _ α hα hα') (odd_weight_positive _ α hα hα')))
    (by positivity)
  refine hb.trans_eq ?_
  calc
    _ = ((45*(rhi:ℝ)*(H:ℝ))*((k-j:ℕ):ℝ)*
        (|(oddSignedFrequency s j:ℝ)+α|^2+2*|(oddSignedFrequency s j:ℝ)+α| *
          ((k-j:ℕ):ℝ)+((k-j:ℕ):ℝ)^2/3))*
        ((qb:ℝ)^(k-j)*(a:ℝ)^((k:ℤ)-(j:ℤ))) := by ring
    _ = _ := by rw [odd_upper_geometric_identity j k (le_of_lt hk)]; ring

theorem odd_cross_weighted_bound (s : ℤ) (hs : s = 1 ∨ s = -1) (j k : ℕ)
    (hj : 3 ≤ j) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    oddSignedRow α s j (-s) k ≤
      (45*(rhi:ℝ)*(H:ℝ))*(37/16)*(qb:ℝ)*((qb/a:ℚ):ℝ)^j*
        (|(oddSignedFrequency s j:ℝ)+α|+(k:ℝ))*
        (2*|(oddSignedFrequency s j:ℝ)+α|+(k:ℝ))^2*((qb*a:ℚ):ℝ)^k := by
  have hsneg : -s = 1 ∨ -s = -1 := by rcases hs with rfl | rfl <;> norm_num
  rw [odd_signed_row_off α s (-s) j k (odd_cross_frequency_ne s hs j k)]
  have he := odd_cross_entry_bound s hs j k (by omega) α hα hα'
  have hw := odd_cross_branch_weight_ratio s (-s) hs hsneg j k hj α hα hα'
  have hH : 0 ≤ (H:ℝ) := by norm_num [H, rhi, qb]
  have hq : 0 ≤ (qb:ℝ) := by norm_num [qb]
  have hr : 0 ≤ (rhi:ℝ) := by norm_num [rhi]
  have hb := mul_le_mul he hw
    (le_of_lt (div_pos (odd_weight_positive _ α hα hα') (odd_weight_positive _ α hα hα')))
    (by positivity)
  refine hb.trans_eq ?_
  calc
    _ = ((45*(rhi:ℝ)*(H:ℝ))*(37/16)*
        (|(oddSignedFrequency s j:ℝ)+α|+(k:ℝ))*(2*|(oddSignedFrequency s j:ℝ)+α|+(k:ℝ))^2)*
        ((qb:ℝ)^(j+k+1)*(a:ℝ)^((k:ℤ)-(j:ℤ))) := by ring
    _ = _ := by rw [odd_cross_geometric_identity]; ring

end Lemniscate.OddArithmetic
