import Lemniscate.OddHighBranchSums

/-! The entire high odd row, indexed by all integer Fourier modes, is controlled
by the previously certified quartic at the actual shifted frequency. -/
namespace Lemniscate.OddArithmetic
open CoarseArithmetic

theorem odd_full_row_from_branches (s : ℤ) (hs : s = 1 ∨ s = -1) (j : ℕ)
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2)
    (hself : Summable (oddSignedRow α s j s)) (hcross : Summable (oddSignedRow α s j (-s))) :
    Summable (oddOffIndexRow α (oddSignedFrequency s j)) ∧
    (∑' k : ℤ, oddOffIndexRow α (oddSignedFrequency s j) k)/oddWeight (oddSignedFrequency s j) α =
      (∑' k : ℕ, oddSignedRow α s j s k)+(∑' k : ℕ, oddSignedRow α s j (-s) k) := by
  have hp : Summable (oddSignedRow α s j 1) := by
    rcases hs with rfl | rfl
    · exact hself
    · simpa only [neg_neg] using hcross
  have hn : Summable (oddSignedRow α s j (-1)) := by
    rcases hs with rfl | rfl
    · exact hcross
    · exact hself
  let f : ℤ → ℝ := fun k => oddOffIndexRow α (oddSignedFrequency s j) k/
    oddWeight (oddSignedFrequency s j) α
  have he (k : ℕ) : 2*(-((k:ℤ)+1))+1 = -(2*(k:ℤ)+1) := by ring
  have hfp : Summable (fun k : ℕ => f (k:ℤ)) := by
    change Summable (fun k : ℕ => oddSignedRow α s j 1 k) at hp
    simpa only [f, oddOffIndexRow, oddSignedRow, oddSignedFrequency, one_mul] using hp
  have hfn : Summable (fun k : ℕ => f (-((k:ℤ)+1))) := by
    change Summable (fun k : ℕ => oddSignedRow α s j (-1) k) at hn
    simpa only [f, oddOffIndexRow, oddSignedRow, oddSignedFrequency, neg_one_mul, he] using hn
  have hf : Summable f := Summable.of_nat_of_neg_add_one hfp hfn
  have hw := odd_weight_positive (oddSignedFrequency s j) α hα hα'
  have heq : (fun k : ℤ => f k*oddWeight (oddSignedFrequency s j) α) =
      oddOffIndexRow α (oddSignedFrequency s j) := by
    funext k
    dsimp only [f]
    exact div_mul_cancel₀ _ (ne_of_gt hw)
  refine ⟨by rw [← heq]; exact hf.mul_right _, ?_⟩
  have hsum := tsum_of_nat_of_neg_add_one hfp hfn
  have hsum' : (∑' k : ℤ, oddOffIndexRow α (oddSignedFrequency s j) k)/oddWeight (oddSignedFrequency s j) α =
      (∑' k : ℕ, oddSignedRow α s j 1 k)+(∑' k : ℕ, oddSignedRow α s j (-1) k) := by
    simpa only [f, oddOffIndexRow, oddSignedRow, oddSignedFrequency, one_mul,
      neg_one_mul, he, tsum_div_const] using hsum
  rcases hs with rfl | rfl
  · exact hsum'
  · simpa only [neg_neg, add_comm] using hsum'

theorem odd_diagonal_high_bound (n : ℤ) (α : ℝ) :
    oddMatrixEntry α n n ≤
      -4*(rlo:ℝ)^2*|(n:ℝ)+α|^4+45*(rhi:ℝ)*|(n:ℝ)+α|^2 := by
  have hd := odd_matrix_diagonal_bound α n
  have h0 : (hUpper 0:ℝ) ≤ 1 := by exact_mod_cast coarse_h0_le_one
  have hp := mul_le_mul_of_nonneg_left h0 (by
    have hr : 0 ≤ (rhi:ℝ) := by norm_num [rhi]
    positivity : 0 ≤ 45*(rhi:ℝ)*((n:ℝ)+α)^2)
  have h4 : |(n:ℝ)+α|^4 = ((n:ℝ)+α)^4 := by
    calc
      _ = (|(n:ℝ)+α|^2)^2 := by ring
      _ = (((n:ℝ)+α)^2)^2 := by rw [sq_abs]
      _ = _ := by ring
  rw [h4, sq_abs]
  nlinarith

theorem odd_high_row_quartic_bound (s : ℤ) (hs : s = 1 ∨ s = -1) (j : ℕ) (hj : 6 ≤ j)
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    Summable (oddOffIndexRow α (oddSignedFrequency s j)) ∧
    oddMatrixEntry α (oddSignedFrequency s j) (oddSignedFrequency s j)+
      (∑' k : ℤ, oddOffIndexRow α (oddSignedFrequency s j) k)/oddWeight (oddSignedFrequency s j) α ≤
        HighFrequency.realValue HighFrequency.odd |(oddSignedFrequency s j:ℝ)+α| := by
  have hself := odd_same_branch_sum_bound s hs j (by omega) α hα hα'
  have hcross := odd_cross_branch_sum_bound s hs j hj α hα hα'
  have hfull := odd_full_row_from_branches s hs j α hα hα' hself.1 hcross.1
  refine ⟨hfull.1, ?_⟩
  rw [hfull.2]
  have hb := add_le_add (odd_diagonal_high_bound (oddSignedFrequency s j) α)
    (add_le_add hself.2 (le_of_lt hcross.2))
  refine hb.trans_eq ?_
  simp only [HighFrequency.realValue, HighFrequency.odd, HighFrequency.E,
    HighFrequency.s2, HighFrequency.s1, HighFrequency.s0, shiftedQuartic,
    Rat.cast_mul, Rat.cast_add, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero,
    sub_zero]
  ring

theorem odd_high_rows_dissipative (s : ℤ) (hs : s = 1 ∨ s = -1) (j : ℕ) (hj : 6 ≤ j)
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    Summable (oddOffIndexRow α (oddSignedFrequency s j)) ∧
    oddMatrixEntry α (oddSignedFrequency s j) (oddSignedFrequency s j)+
      (∑' k : ℤ, oddOffIndexRow α (oddSignedFrequency s j) k)/oddWeight (oddSignedFrequency s j) α <
        -3112 := by
  have ht := odd_high_row_quartic_bound s hs j hj α hα hα'
  have hf := (odd_signed_shift_bounds s hs j α hα hα').1
  have hjr : (6:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  exact ⟨ht.1, ht.2.trans_lt (HighFrequency.odd_high_bound _ (by linarith))⟩

end Lemniscate.OddArithmetic
