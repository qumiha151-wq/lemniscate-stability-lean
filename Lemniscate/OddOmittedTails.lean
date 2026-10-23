import Lemniscate.OddEntryTails
import Lemniscate.GeometricTails

/-! Convergence and rational upper bounds for both omitted infinite column tails
of the twelve low odd rows. Each sign is summed from column magnitude 27. -/
namespace Lemniscate.OddArithmetic
open CoarseArithmetic

def oddOmittedColumn (s : ℤ) (k : ℕ) : ℤ := s*(27+2*(k:ℤ))

theorem odd_omitted_column_odd (s : ℤ) (hs : s = 1 ∨ s = -1) (k : ℕ) :
    Odd (oddOmittedColumn s k) := by
  rcases hs with rfl | rfl
  · exact ⟨13+(k:ℤ), by simp [oddOmittedColumn]; ring⟩
  · exact ⟨-14-(k:ℤ), by simp [oddOmittedColumn]; ring⟩

theorem odd_omitted_column_abs (s : ℤ) (hs : s = 1 ∨ s = -1) (k : ℕ) :
    (oddOmittedColumn s k).natAbs = 27+2*k := by
  have hp : 27+2*(k:ℤ) = ((27+2*k:ℕ):ℤ) := by push_cast; ring
  rcases hs with rfl | rfl <;>
    simp only [oddOmittedColumn, one_mul, neg_one_mul, hp, Int.natAbs_neg, Int.natAbs_natCast]

theorem odd_omitted_index_data (i : Fin 12) (s : ℤ) (hs : s = 1 ∨ s = -1) (k : ℕ) :
    lowIndex i ≠ oddOmittedColumn s k ∧
    (lowIndex i-oddOmittedColumn s k).natAbs/2 = k+((27-s*lowIndex i)/2).toNat ∧
    (s*lowIndex i-7)/2+(((27-s*lowIndex i)/2).toNat:ℤ) = 10 := by
  have hi := i.isLt
  rcases hs with rfl | rfl
  · have he : lowIndex i-oddOmittedColumn 1 k = -((38-2*i.val+2*k:ℕ):ℤ) := by
      simp only [lowIndex, oddOmittedColumn, one_mul]
      omega
    rw [he, Int.natAbs_neg, Int.natAbs_natCast]
    simp only [lowIndex, oddOmittedColumn, one_mul]
    omega
  · have he : lowIndex i-oddOmittedColumn (-1) k = ((16+2*i.val+2*k:ℕ):ℤ) := by
      simp only [lowIndex, oddOmittedColumn, neg_one_mul]
      omega
    rw [he, Int.natAbs_natCast]
    simp only [lowIndex, oddOmittedColumn, neg_one_mul]
    omega

theorem odd_omitted_majorant_hasSum (n s : ℤ) :
    HasSum (fun k : ℕ =>
      let L := ((27-s*n)/2).toNat
      let j : ℝ := (k+L:ℕ)
      let v : ℝ := (n.natAbs:ℝ)+1/2
      (45*(rhi:ℝ)*(H:ℝ))*(3/250)*(a:ℝ)^((s*n-7)/2)*
        j*((qb*a:ℚ):ℝ)^(k+L)*(v^2+2*v*j+j^2/3))
      (omittedOneSign n s:ℝ) := by
  let L := ((27-s*n)/2).toNat
  let v : ℝ := (n.natAbs:ℝ)+1/2
  have hz : ‖((qb*a:ℚ):ℝ)‖ < 1 := by norm_num [qb, a]
  convert! ((((tail1_sound (qb*a) hz L).mul_left (v^2)).add
    ((tail2_sound (qb*a) hz L).mul_left (2*v))).add
    ((tail3_sound (qb*a) hz L).mul_left (1/3))).mul_left
    ((45*(rhi:ℝ)*(H:ℝ))*(3/250)*(a:ℝ)^((s*n-7)/2)) using 1
  · ext k
    dsimp only [L, v]
    ring
  · simp only [omittedOneSign, Rat.cast_mul, Rat.cast_add, Rat.cast_pow,
      Rat.cast_zpow, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
    dsimp only [v, L]
    ring

theorem odd_omitted_weighted_entry_bound (i : Fin 12) (s : ℤ)
    (hs : s = 1 ∨ s = -1) (k : ℕ) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    |oddMatrixEntry α (lowIndex i) (oddOmittedColumn s k)| *
        oddWeight (oddOmittedColumn s k) α ≤
      let n := lowIndex i
      let L := ((27-s*n)/2).toNat
      let j : ℝ := (k+L:ℕ)
      let v : ℝ := (n.natAbs:ℝ)+1/2
      (45*(rhi:ℝ)*(H:ℝ))*(3/250)*(a:ℝ)^((s*n-7)/2)*
        j*((qb*a:ℚ):ℝ)^(k+L)*(v^2+2*v*j+j^2/3) := by
  obtain ⟨hne, hd, he⟩ := odd_omitted_index_data i s hs k
  have hm := odd_omitted_column_abs s hs k
  have hw := odd_weight_high_upper (oddOmittedColumn s k) α (by omega) hα hα'
  have hb := odd_matrix_off_tail_bound (lowIndex i) (oddOmittedColumn s k)
    (lowIndex_odd i) (odd_omitted_column_odd s hs k) hne α hα hα'
  have ha : 0 < (a:ℝ) := by norm_num [a]
  have hp : (a:ℝ)^((s*lowIndex i-7)/2)*(a:ℝ)^(k+((27-s*lowIndex i)/2).toNat) =
      (a:ℝ)^(10+k) := by
    rw [← zpow_natCast, ← zpow_add₀ (ne_of_gt ha)]
    rw [show (s*lowIndex i-7)/2+((k+((27-s*lowIndex i)/2).toNat:ℕ):ℤ) =
      ((10+k:ℕ):ℤ) by omega, zpow_natCast]
  rw [hm, show (27+2*k-7)/2 = 10+k by omega] at hw
  have hn : |(lowIndex i:ℝ)| = ((lowIndex i).natAbs:ℝ) := by
    have ht := congrArg (fun z : ℤ => (z:ℝ)) (Int.natCast_natAbs (lowIndex i))
    simpa only [Int.cast_natCast, Int.cast_abs] using ht.symm
  rw [hd, hn] at hb
  have ht := mul_le_mul hb hw
    (le_of_lt (odd_weight_positive (oddOmittedColumn s k) α hα hα')) (by
      have hH : 0 ≤ (H:ℝ) := by norm_num [H, rhi, qb]
      have hq : 0 ≤ (qb:ℝ) := by norm_num [qb]
      have hr : 0 ≤ (rhi:ℝ) := by norm_num [rhi]
      positivity)
  refine ht.trans_eq ?_
  dsimp only
  rw [Rat.cast_mul, mul_pow, ← hp]
  ring

theorem odd_omitted_tail_bound (i : Fin 12) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    Summable (fun k : ℕ => |oddMatrixEntry α (lowIndex i) (oddOmittedColumn s k)| *
      oddWeight (oddOmittedColumn s k) α) ∧
    (∑' k : ℕ, |oddMatrixEntry α (lowIndex i) (oddOmittedColumn s k)| *
      oddWeight (oddOmittedColumn s k) α) ≤ (omittedOneSign (lowIndex i) s:ℝ) := by
  have hn (k : ℕ) : 0 ≤ |oddMatrixEntry α (lowIndex i) (oddOmittedColumn s k)| *
      oddWeight (oddOmittedColumn s k) α :=
    mul_nonneg (abs_nonneg _) (le_of_lt (odd_weight_positive _ α hα hα'))
  have hm := fun k => odd_omitted_weighted_entry_bound i s hs k α hα hα'
  have hsum := odd_omitted_majorant_hasSum (lowIndex i) s
  have habs := Summable.of_nonneg_of_le hn hm hsum.summable
  exact ⟨habs, by simpa only [hsum.tsum_eq] using habs.tsum_le_tsum hm hsum.summable⟩

noncomputable def oddActualOmitted (n : ℤ) (α : ℝ) : ℝ :=
  (∑' k : ℕ, |oddMatrixEntry α n (oddOmittedColumn (-1) k)| *
    oddWeight (oddOmittedColumn (-1) k) α)+
  (∑' k : ℕ, |oddMatrixEntry α n (oddOmittedColumn 1 k)| *
    oddWeight (oddOmittedColumn 1 k) α)

theorem odd_large_column_representation (m : ℤ) (hm : Odd m) (hlarge : 27 ≤ m.natAbs) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∃ k : ℕ, m = oddOmittedColumn s k := by
  rcases hm with ⟨j, hj⟩
  cases m with
  | ofNat m =>
    refine ⟨1, Or.inl rfl, (m-27)/2, ?_⟩
    simp only [oddOmittedColumn, one_mul]
    simp only [Int.ofNat_eq_natCast] at hj ⊢
    have hmge : 27 ≤ m := hlarge
    have hpar : m % 2 = 1 := by omega
    have he : m = 27+2*((m-27)/2) := by omega
    exact_mod_cast he
  | negSucc m =>
    refine ⟨-1, Or.inr rfl, (m+1-27)/2, ?_⟩
    simp only [oddOmittedColumn, neg_one_mul]
    simp only [Int.natAbs_negSucc] at hlarge
    omega

theorem odd_actual_omitted_le (i : Fin 12) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    oddActualOmitted (lowIndex i) α ≤ (omitted (lowIndex i):ℝ) := by
  have hn := (odd_omitted_tail_bound i (-1) (Or.inr rfl) α hα hα').2
  have hp := (odd_omitted_tail_bound i 1 (Or.inl rfl) α hα hα').2
  unfold oddActualOmitted omitted
  rw [Rat.cast_add]
  exact add_le_add hn hp

theorem odd_low_complete_head_tail_bound (i : Fin 12) (α : ℝ)
    (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    oddMatrixEntry α (lowIndex i) (lowIndex i)*oddWeight (lowIndex i) α+
      oddActualHead (lowIndex i) α+oddActualOmitted (lowIndex i) α ≤
        -oddWeight (lowIndex i) α-1/2 := by
  have hh := odd_low_row_with_omitted_bound i α hα hα'
  have ht := odd_actual_omitted_le i α hα hα'
  linarith

theorem odd_zero_complete_head_tail_bound (i : Fin 12) :
    oddMatrixEntry 0 (lowIndex i) (lowIndex i)*oddWeight (lowIndex i) 0+
      oddActualHead (lowIndex i) 0+oddActualOmitted (lowIndex i) 0 <
        -6*oddWeight (lowIndex i) 0 := by
  have hh := odd_zero_row_with_omitted_bound i
  have ht := odd_actual_omitted_le i 0 (by norm_num) (by norm_num)
  linarith

end Lemniscate.OddArithmetic
