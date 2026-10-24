import Lemniscate.OddSignedWeights

/-! Actual half-distances and shifted absolute frequencies on the two signed
odd branches. All parameter estimates retain both endpoints of [0,1/2]. -/
namespace Lemniscate.OddArithmetic
open CoarseArithmetic

theorem odd_signed_shift_abs (s : ℤ) (hs : s = 1 ∨ s = -1) (j : ℕ)
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    |(oddSignedFrequency s j:ℝ)+α| = 2*(j:ℝ)+1+(s:ℝ)*α := by
  have hj : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
  rcases hs with rfl | rfl
  · norm_num [oddSignedFrequency]
    positivity
  · norm_num [oddSignedFrequency]
    rw [abs_of_nonpos (by linarith : -1+ -(2*(j:ℝ))+α ≤ 0)]
    ring

theorem odd_signed_shift_bounds (s : ℤ) (hs : s = 1 ∨ s = -1) (j : ℕ)
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    2*(j:ℝ)+1/2 ≤ |(oddSignedFrequency s j:ℝ)+α| ∧
      |(oddSignedFrequency s j:ℝ)+α| ≤ 2*(j:ℝ)+3/2 := by
  rw [odd_signed_shift_abs s hs j α hα hα']
  rcases hs with rfl | rfl <;> norm_num <;> constructor <;> linarith

theorem odd_same_half_distance_lower (s : ℤ) (hs : s = 1 ∨ s = -1) (j k : ℕ)
    (hk : k ≤ j) :
    (oddSignedFrequency s j-oddSignedFrequency s k).natAbs/2 = j-k := by
  rcases hs with rfl | rfl
  · have he : oddSignedFrequency 1 j-oddSignedFrequency 1 k = ((2*(j-k):ℕ):ℤ) := by
      simp only [oddSignedFrequency, one_mul]
      omega
    rw [he, Int.natAbs_natCast, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  · have he : oddSignedFrequency (-1) j-oddSignedFrequency (-1) k = -((2*(j-k):ℕ):ℤ) := by
      simp only [oddSignedFrequency, neg_one_mul]
      omega
    rw [he, Int.natAbs_neg, Int.natAbs_natCast, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

theorem odd_same_half_distance_upper (s : ℤ) (hs : s = 1 ∨ s = -1) (j k : ℕ)
    (hk : j ≤ k) :
    (oddSignedFrequency s j-oddSignedFrequency s k).natAbs/2 = k-j := by
  rw [show oddSignedFrequency s j-oddSignedFrequency s k =
    -(oddSignedFrequency s k-oddSignedFrequency s j) by omega, Int.natAbs_neg]
  exact odd_same_half_distance_lower s hs k j hk

theorem odd_cross_half_distance (s : ℤ) (hs : s = 1 ∨ s = -1) (j k : ℕ) :
    (oddSignedFrequency s j-oddSignedFrequency (-s) k).natAbs/2 = j+k+1 := by
  rcases hs with rfl | rfl
  · have he : oddSignedFrequency 1 j-oddSignedFrequency (-1) k = ((2*(j+k+1):ℕ):ℤ) := by
      simp only [oddSignedFrequency, one_mul, neg_one_mul]
      omega
    rw [he, Int.natAbs_natCast, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  · have he : oddSignedFrequency (-1) j-oddSignedFrequency (-(-1)) k = -((2*(j+k+1):ℕ):ℤ) := by
      simp only [oddSignedFrequency, one_mul, neg_one_mul, neg_neg]
      omega
    rw [he, Int.natAbs_neg, Int.natAbs_natCast, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

theorem odd_signed_frequency_injective (s : ℤ) (hs : s = 1 ∨ s = -1) :
    Function.Injective (oddSignedFrequency s) := by
  intro j k he
  rcases hs with rfl | rfl <;> simp only [oddSignedFrequency, one_mul, neg_one_mul] at he <;> omega

theorem odd_cross_frequency_ne (s : ℤ) (hs : s = 1 ∨ s = -1) (j k : ℕ) :
    oddSignedFrequency s j ≠ oddSignedFrequency (-s) k := by
  have hd := odd_cross_half_distance s hs j k
  intro he
  rw [he, sub_self, Int.natAbs_zero, Nat.zero_div] at hd
  omega

theorem odd_lower_polynomial_identity (s : ℤ) (hs : s = 1 ∨ s = -1) (j k : ℕ)
    (hk : k ≤ j) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    oddEntryPolynomial (oddSignedFrequency s j) (oddSignedFrequency s k) α =
      45*(|(oddSignedFrequency s j:ℝ)+α|^2-
        2*|(oddSignedFrequency s j:ℝ)+α| * ((j-k:ℕ):ℝ)-((j-k:ℕ):ℝ)^2/3) := by
  rw [odd_signed_shift_abs s hs j α hα hα', Nat.cast_sub hk]
  rcases hs with rfl | rfl <;>
    norm_num [oddEntryPolynomial, oddSignedFrequency] <;> ring

theorem odd_lower_polynomial_bound (v l : ℝ) (hv : 0 ≤ v) (hl : 0 ≤ l) (hlv : 2*l ≤ v) :
    |v^2-2*v*l-l^2/3| ≤ v^2 := by
  have hprod := mul_nonneg (by linarith : 0 ≤ v-2*l) (by linarith : 0 ≤ v+2*l)
  have hvl := mul_le_mul_of_nonneg_left hlv hv
  have hvln := mul_nonneg hv hl
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg v, sq_nonneg l]

end Lemniscate.OddArithmetic
