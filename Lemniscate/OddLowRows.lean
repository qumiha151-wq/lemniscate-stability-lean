import Lemniscate.OddOmittedTails

/-! Full integer-indexed low odd rows. Index k corresponds to the odd Fourier
frequency 2*k+1; the diagonal is excluded from the absolutely summable row. -/
namespace Lemniscate.OddArithmetic
open CoarseArithmetic

noncomputable def oddWeightedOffEntry (α : ℝ) (n m : ℤ) : ℝ :=
  if m = n then 0 else |oddMatrixEntry α n m| * oddWeight m α

noncomputable def oddOffIndexRow (α : ℝ) (n k : ℤ) : ℝ :=
  oddWeightedOffEntry α n (2*k+1)

theorem odd_head_sum_split (f : ℤ → ℝ) :
    (∑ m ∈ oddIndices.toFinset, f m) =
      (∑ k ∈ Finset.range 13, f (2*(k:ℤ)+1))+
      (∑ k ∈ Finset.range 13, f (-(2*(k:ℤ)+1))) := by
  norm_num [oddIndices, List.range_succ, Finset.sum_range_succ]
  ring

theorem odd_low_row_tail_eq (i : Fin 12) (s : ℤ) (hs : s = 1 ∨ s = -1) (α : ℝ) :
    (fun k : ℕ => oddWeightedOffEntry α (lowIndex i) (s*(2*((k+13:ℕ):ℤ)+1))) =
      (fun k : ℕ => |oddMatrixEntry α (lowIndex i) (oddOmittedColumn s k)| *
        oddWeight (oddOmittedColumn s k) α) := by
  funext k
  have he : s*(2*((k+13:ℕ):ℤ)+1) = oddOmittedColumn s k := by
    unfold oddOmittedColumn
    push_cast
    ring
  rw [he, oddWeightedOffEntry, if_neg (Ne.symm (odd_omitted_index_data i s hs k).1)]

theorem odd_low_row_side_summable (i : Fin 12) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    Summable (fun k : ℕ => oddWeightedOffEntry α (lowIndex i) (s*(2*(k:ℤ)+1))) := by
  apply (summable_nat_add_iff 13).mp
  rw [odd_low_row_tail_eq i s hs α]
  exact (odd_omitted_tail_bound i s hs α hα hα').1

theorem odd_low_full_row_summable (i : Fin 12) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    Summable (oddOffIndexRow α (lowIndex i)) := by
  apply Summable.of_nat_of_neg_add_one
  · simpa only [oddOffIndexRow, one_mul] using
      odd_low_row_side_summable i 1 (Or.inl rfl) α hα hα'
  · have he (k : ℕ) : 2*(-((k:ℤ)+1))+1 = -(2*(k:ℤ)+1) := by ring
    simpa only [oddOffIndexRow, he, neg_one_mul] using
      odd_low_row_side_summable i (-1) (Or.inr rfl) α hα hα'

theorem odd_low_full_row_sum (i : Fin 12) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    (∑' k : ℤ, oddOffIndexRow α (lowIndex i) k) =
      oddActualHead (lowIndex i) α+oddActualOmitted (lowIndex i) α := by
  have hp := odd_low_row_side_summable i 1 (Or.inl rfl) α hα hα'
  have hn := odd_low_row_side_summable i (-1) (Or.inr rfl) α hα hα'
  have hp' : Summable (fun k : ℕ => oddOffIndexRow α (lowIndex i) (k:ℤ)) := by
    simpa only [oddOffIndexRow, one_mul] using hp
  have he (k : ℕ) : 2*(-((k:ℤ)+1))+1 = -(2*(k:ℤ)+1) := by ring
  have hn' : Summable (fun k : ℕ => oddOffIndexRow α (lowIndex i) (-((k:ℤ)+1))) := by
    simpa only [oddOffIndexRow, he, neg_one_mul] using hn
  rw [tsum_of_nat_of_neg_add_one hp' hn']
  simp only [oddOffIndexRow, he]
  simp only [one_mul] at hp
  simp only [neg_one_mul] at hn
  rw [← hp.sum_add_tsum_nat_add 13, ← hn.sum_add_tsum_nat_add 13]
  have htp := odd_low_row_tail_eq i 1 (Or.inl rfl) α
  have htn := odd_low_row_tail_eq i (-1) (Or.inr rfl) α
  simp only [one_mul] at htp
  simp only [neg_one_mul] at htn
  rw [htp, htn]
  have hh := odd_head_sum_split (oddWeightedOffEntry α (lowIndex i))
  change oddActualHead (lowIndex i) α = _ at hh
  rw [hh, oddActualOmitted]
  ring

theorem odd_low_rows_dissipative (i : Fin 12) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    Summable (oddOffIndexRow α (lowIndex i)) ∧
    oddMatrixEntry α (lowIndex i) (lowIndex i)+
      (∑' k : ℤ, oddOffIndexRow α (lowIndex i) k)/oddWeight (lowIndex i) α < -1 := by
  refine ⟨odd_low_full_row_summable i α hα hα', ?_⟩
  have hw := odd_weight_positive (lowIndex i) α hα hα'
  have hb := odd_low_complete_head_tail_bound i α hα hα'
  rw [odd_low_full_row_sum i α hα hα']
  calc
    _ = (oddMatrixEntry α (lowIndex i) (lowIndex i)*oddWeight (lowIndex i) α+
        (oddActualHead (lowIndex i) α+oddActualOmitted (lowIndex i) α))/
          oddWeight (lowIndex i) α := by field_simp [ne_of_gt hw]
    _ < -1 := (div_lt_iff₀ hw).mpr (by linarith)

theorem odd_zero_low_rows_dissipative (i : Fin 12) :
    oddMatrixEntry 0 (lowIndex i) (lowIndex i)+
      (∑' k : ℤ, oddOffIndexRow 0 (lowIndex i) k)/oddWeight (lowIndex i) 0 < -6 := by
  have hw := odd_weight_positive (lowIndex i) 0 (by norm_num) (by norm_num)
  have hb := odd_zero_complete_head_tail_bound i
  rw [odd_low_full_row_sum i 0 (by norm_num) (by norm_num)]
  have ht : (oddMatrixEntry 0 (lowIndex i) (lowIndex i)*oddWeight (lowIndex i) 0+
      (oddActualHead (lowIndex i) 0+oddActualOmitted (lowIndex i) 0))/
        oddWeight (lowIndex i) 0 < -6 := (div_lt_iff₀ hw).mpr (by linarith)
  have he : (oddMatrixEntry 0 (lowIndex i) (lowIndex i)*oddWeight (lowIndex i) 0+
      (oddActualHead (lowIndex i) 0+oddActualOmitted (lowIndex i) 0))/
        oddWeight (lowIndex i) 0 = oddMatrixEntry 0 (lowIndex i) (lowIndex i)+
      (oddActualHead (lowIndex i) 0+oddActualOmitted (lowIndex i) 0)/oddWeight (lowIndex i) 0 := by
    field_simp [ne_of_gt hw]
  rw [he] at ht
  exact ht

end Lemniscate.OddArithmetic
