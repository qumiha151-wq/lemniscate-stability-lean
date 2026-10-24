import Lemniscate.OddLowRows

/-! Signed frequency indices and geometric weight ratios for every column of a
high odd row, including the three exceptional low frequencies on each branch. -/
namespace Lemniscate.OddArithmetic
open CoarseArithmetic

def oddSignedFrequency (s : ℤ) (j : ℕ) : ℤ := s*(2*(j:ℤ)+1)

theorem odd_signed_frequency_odd (s : ℤ) (hs : s = 1 ∨ s = -1) (j : ℕ) :
    Odd (oddSignedFrequency s j) := by
  rcases hs with rfl | rfl
  · exact ⟨j, by simp [oddSignedFrequency]⟩
  · exact ⟨-(j:ℤ)-1, by simp [oddSignedFrequency]; ring⟩

theorem odd_signed_frequency_abs (s : ℤ) (hs : s = 1 ∨ s = -1) (j : ℕ) :
    (oddSignedFrequency s j).natAbs = 2*j+1 := by
  have he : 2*(j:ℤ)+1 = ((2*j+1:ℕ):ℤ) := by push_cast; ring
  rcases hs with rfl | rfl <;>
    simp only [oddSignedFrequency, one_mul, neg_one_mul, he, Int.natAbs_neg, Int.natAbs_natCast]

theorem odd_signed_frequency_base (s : ℤ) (hs : s = 1 ∨ s = -1) (j : ℕ) (α : ℝ) :
    oddWeightBase (oddSignedFrequency s j) α = oddWeightBase s α := by
  rcases hs with rfl | rfl
  · have hp : (0:ℤ) < 2*(j:ℤ)+1 := by omega
    norm_num [oddWeightBase, oddSignedFrequency, hp]
  · have hn : ¬ 2*(j:ℤ) < -1 := by omega
    norm_num [oddWeightBase, oddSignedFrequency, hn]

theorem odd_signed_weight_high (s : ℤ) (hs : s = 1 ∨ s = -1) (j : ℕ) (hj : 3 ≤ j)
    (α : ℝ) : oddWeight (oddSignedFrequency s j) α =
      (3/25:ℝ)*(a:ℝ)^((j:ℤ)-3)*oddWeightBase s α := by
  have ha := odd_signed_frequency_abs s hs j
  rw [odd_weight_high _ α (by omega), ha, odd_signed_frequency_base s hs j α]
  have he : (2*j+1-7)/2 = j-3 := by omega
  rw [he]
  have hc : ((j-3:ℕ):ℤ) = (j:ℤ)-3 := by omega
  rw [← hc, zpow_natCast]

theorem odd_signed_weight_envelope (s : ℤ) (hs : s = 1 ∨ s = -1) (j : ℕ)
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    oddWeight (oddSignedFrequency s j) α ≤
      (3/25:ℝ)*(a:ℝ)^((j:ℤ)-3)*oddWeightBase s α := by
  by_cases hj : 3 ≤ j
  · exact le_of_eq (odd_signed_weight_high s hs j hj α)
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hs with rfl | rfl <;> rcases hcases with rfl | rfl | rfl
  · have hb := (odd_positive_base_bounds α hα hα').1
    norm_num [oddSignedFrequency, odd_weight_one, oddWeightBase, a]
    linarith
  · norm_num [oddSignedFrequency, odd_weight_three, oddWeightBase, oddPositiveBase, a]
    nlinarith [sq_nonneg (α-1/2)]
  · rw [show oddSignedFrequency 1 2 = 5 by norm_num [oddSignedFrequency],
      odd_weight_other 5 α (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    have hb := (odd_positive_base_bounds α hα hα').1
    norm_num [oddWeightBase, a]
    linarith
  · norm_num [oddSignedFrequency, odd_weight_neg_one, oddWeightBase, oddNegativeBase, a]
    nlinarith [sq_nonneg α]
  · norm_num [oddSignedFrequency, odd_weight_neg_three, oddWeightBase, oddNegativeBase, a]
    nlinarith [sq_nonneg α]
  · rw [show oddSignedFrequency (-1) 2 = -5 by norm_num [oddSignedFrequency],
      odd_weight_other (-5) α (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    have hb := (odd_negative_base_bounds α hα hα').1
    norm_num [oddWeightBase, a]
    linarith

theorem odd_signed_weight_ratio (s t : ℤ) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1)
    (j k : ℕ) (hj : 3 ≤ j) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2)
    (c : ℝ) (hc : oddWeightBase t α ≤ c*oddWeightBase s α) :
    oddWeight (oddSignedFrequency t k) α/oddWeight (oddSignedFrequency s j) α ≤
      c*(a:ℝ)^((k:ℤ)-(j:ℤ)) := by
  have hw := odd_weight_positive (oddSignedFrequency s j) α hα hα'
  have ha : 0 < (a:ℝ) := by norm_num [a]
  apply (div_le_iff₀ hw).mpr
  rw [odd_signed_weight_high s hs j hj α]
  calc
    _ ≤ (3/25:ℝ)*(a:ℝ)^((k:ℤ)-3)*oddWeightBase t α :=
      odd_signed_weight_envelope t ht k α hα hα'
    _ ≤ ((3/25:ℝ)*(a:ℝ)^((k:ℤ)-3))*(c*oddWeightBase s α) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by
      have he : (a:ℝ)^((k:ℤ)-(j:ℤ))*(a:ℝ)^((j:ℤ)-3) = (a:ℝ)^((k:ℤ)-3) := by
        rw [← zpow_add₀ (ne_of_gt ha)]
        congr 1
        ring
      rw [← he]
      ring

theorem odd_same_branch_weight_ratio (s : ℤ) (hs : s = 1 ∨ s = -1)
    (j k : ℕ) (hj : 3 ≤ j) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    oddWeight (oddSignedFrequency s k) α/oddWeight (oddSignedFrequency s j) α ≤
      (a:ℝ)^((k:ℤ)-(j:ℤ)) := by
  simpa only [one_mul] using odd_signed_weight_ratio s s hs hs j k hj α hα hα' 1 (by simp)

theorem odd_cross_branch_weight_ratio (s t : ℤ) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1)
    (j k : ℕ) (hj : 3 ≤ j) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    oddWeight (oddSignedFrequency t k) α/oddWeight (oddSignedFrequency s j) α ≤
      (37/16)*(a:ℝ)^((k:ℤ)-(j:ℤ)) :=
  odd_signed_weight_ratio s t hs ht j k hj α hα hα' (37/16)
    (odd_weight_base_ratio t s α hα hα')

end Lemniscate.OddArithmetic
