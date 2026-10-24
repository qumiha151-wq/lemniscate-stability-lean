import Lemniscate.OddHighRows

/-! Every odd row: the complete low-row certificates and high-row quartic cover
all integer odd frequencies, with gaps 1 on [0,1/2] and 6 at zero. -/
namespace Lemniscate.OddArithmetic

theorem odd_frequency_representation (n : ℤ) (hn : Odd n) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∃ j : ℕ, n = oddSignedFrequency s j := by
  rcases hn with ⟨k, hk⟩
  cases n with
  | ofNat n =>
    refine ⟨1, Or.inl rfl, n/2, ?_⟩
    simp only [oddSignedFrequency, one_mul, Int.ofNat_eq_natCast] at hk ⊢
    have hn : n % 2 = 1 := by omega
    have he : n = 2*(n/2)+1 := by omega
    exact_mod_cast he
  | negSucc n =>
    refine ⟨-1, Or.inr rfl, n/2, ?_⟩
    simp only [oddSignedFrequency, neg_one_mul]
    omega

theorem odd_signed_low_index_positive (j : ℕ) (hj : j < 6) :
    oddSignedFrequency 1 j = lowIndex ⟨j+6, by omega⟩ := by
  simp only [oddSignedFrequency, one_mul, lowIndex]
  omega

theorem odd_signed_low_index_negative (j : ℕ) (hj : j < 6) :
    oddSignedFrequency (-1) j = lowIndex ⟨5-j, by omega⟩ := by
  simp only [oddSignedFrequency, neg_one_mul, lowIndex]
  omega

theorem odd_all_rows_dissipative (n : ℤ) (hn : Odd n) (α : ℝ)
    (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    Summable (oddOffIndexRow α n) ∧
    oddMatrixEntry α n n+(∑' k : ℤ, oddOffIndexRow α n k)/oddWeight n α < -1 := by
  obtain ⟨s, hs, j, rfl⟩ := odd_frequency_representation n hn
  by_cases hj : 6 ≤ j
  · have ht := odd_high_rows_dissipative s hs j hj α hα hα'
    exact ⟨ht.1, ht.2.trans (by norm_num)⟩
  · rcases hs with rfl | rfl
    · rw [odd_signed_low_index_positive j (by omega)]
      exact odd_low_rows_dissipative _ α hα hα'
    · rw [odd_signed_low_index_negative j (by omega)]
      exact odd_low_rows_dissipative _ α hα hα'

theorem odd_zero_all_rows_dissipative (n : ℤ) (hn : Odd n) :
    Summable (oddOffIndexRow 0 n) ∧
    oddMatrixEntry 0 n n+(∑' k : ℤ, oddOffIndexRow 0 n k)/oddWeight n 0 < -6 := by
  obtain ⟨s, hs, j, rfl⟩ := odd_frequency_representation n hn
  by_cases hj : 6 ≤ j
  · have ht := odd_high_rows_dissipative s hs j hj 0 (by norm_num) (by norm_num)
    exact ⟨ht.1, ht.2.trans (by norm_num)⟩
  · rcases hs with rfl | rfl
    · rw [odd_signed_low_index_positive j (by omega)]
      exact ⟨odd_low_full_row_summable _ 0 (by norm_num) (by norm_num),
        odd_zero_low_rows_dissipative _⟩
    · rw [odd_signed_low_index_negative j (by omega)]
      exact ⟨odd_low_full_row_summable _ 0 (by norm_num) (by norm_num),
        odd_zero_low_rows_dissipative _⟩

end Lemniscate.OddArithmetic
