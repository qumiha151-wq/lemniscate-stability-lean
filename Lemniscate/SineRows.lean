import Lemniscate.SineHighEntries
import Mathlib.Algebra.BigOperators.Intervals

/-! Complete unit-weight row bounds for the sine tail block on indices j>=2.
The first two rows use exact certificates; every remaining row is covered
uniformly by the quartic bound. -/
namespace Lemniscate.CoarseArithmetic
open Finset

noncomputable def sineOffRow (j k : ℕ) : ℝ :=
  if k < 2 ∨ k = j then 0 else |sineMatrixEntry thetaParameter nome j k|

theorem sine_off_row_nonneg (j k : ℕ) : 0 ≤ sineOffRow j k := by
  unfold sineOffRow
  split_ifs <;> positivity

theorem sine_head_bound (j : ℕ) :
    (∑ k ∈ range 8, sineOffRow j k) ≤
      (sumTo 6 (fun k => if k+2 = j then 0 else absUpper (sineEntry j (k+2))):ℝ) := by
  have hzero : (∑ k ∈ range 2, sineOffRow j k) = 0 := by
    simp [sum_range_succ, sineOffRow]
  have he : (∑ k ∈ range 8, sineOffRow j k) =
      ∑ k ∈ range 6, sineOffRow j (k+2) := by
    rw [show (8:ℕ) = 2+6 by rfl, sum_range_add, hzero, zero_add]
    apply sum_congr rfl
    intro k _
    rw [Nat.add_comm 2 k]
  rw [he, OddArithmetic.sumTo_eq_sum_range, Rat.cast_sum]
  apply sum_le_sum
  intro k _
  by_cases hk : k+2 = j
  · simp [sineOffRow, hk]
  · simpa [sineOffRow, hk, show ¬k+2 < 2 by omega] using
      absUpper_sound _ _ (theta_nome_sine_matrix_enclosure j (k+2))

theorem sine_low_row_bound (j : ℕ) (hj : 2 ≤ j) (hj8 : j < 8) :
    Summable (sineOffRow j) ∧
    sineMatrixEntry thetaParameter nome j j + ∑' k : ℕ, sineOffRow j k ≤ (sineFiniteRow j:ℝ) := by
  have he : (fun n : ℕ => sineOffRow j (n+8)) =
      (fun n : ℕ => |sineMatrixEntry thetaParameter nome j (j+(n+(8-j)))|) := by
    funext n
    rw [show j+(n+(8-j)) = n+8 by omega]
    simp only [sineOffRow, if_neg (by omega : ¬(n+8 < 2 ∨ n+8 = j))]
  have ht := sine_tail_bound j (8-j) (by omega)
  rw [← he] at ht
  have hs : Summable (sineOffRow j) := (summable_nat_add_iff 8).mp ht.1
  refine ⟨hs, ?_⟩
  calc
    _ = sineMatrixEntry thetaParameter nome j j +
        ((∑ k ∈ range 8, sineOffRow j k)+(∑' n : ℕ, sineOffRow j (n+8))) := by
      rw [hs.sum_add_tsum_nat_add 8]
    _ ≤ ((sineEntry j j).hi:ℝ) +
        ((sumTo 6 (fun k => if k+2 = j then 0 else absUpper (sineEntry j (k+2))):ℝ)+
          (entryTailBound j (8-j):ℝ)) :=
      add_le_add (theta_nome_sine_matrix_enclosure j j).2 (add_le_add (sine_head_bound j) ht.2)
    _ = _ := by
      simp only [sineFiniteRow, entryTailBound, Rat.cast_add, Rat.cast_mul,
        Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat]
      ring

set_option maxRecDepth 100000 in
theorem unit_tail_one_values :
    tail1 qb 1 = moment 1 qb ∧ tail2 qb 1 = moment 2 qb ∧
      tail3 qb 1 = moment 3 qb := by decide +kernel

theorem unit_lower_geometric_sum_bound (j : ℕ) :
    (∑ k ∈ range j, ((j-k:ℕ):ℝ)*(qb:ℝ)^(j-k)) ≤ (moment 1 qb:ℝ) := by
  have ht : HasSum (fun k : ℕ => ((k+1:ℕ):ℝ)*(qb:ℝ)^(k+1)) (moment 1 qb:ℝ) := by
    simpa only [unit_tail_one_values.1] using
      tail1_sound qb (by norm_num [qb]) 1
  have hq : (0:ℝ) ≤ (qb:ℝ) := by norm_num [qb]
  calc
    _ = ∑ k ∈ range j, ((j-1-k+1:ℕ):ℝ)*(qb:ℝ)^(j-1-k+1) := by
      apply sum_congr rfl
      intro k hk
      rw [show j-k = j-1-k+1 by have := mem_range.mp hk; omega]
    _ = ∑ k ∈ range j, ((k+1:ℕ):ℝ)*(qb:ℝ)^(k+1) :=
      sum_range_reflect (fun k => ((k+1:ℕ):ℝ)*(qb:ℝ)^(k+1)) j
    _ ≤ _ := sum_le_hasSum (range j) (fun k _ => by positivity) ht

theorem sine_lower_sum_bound (j : ℕ) :
    (∑ k ∈ range j, sineOffRow j k) ≤ (C:ℝ)*(2*(j:ℝ))^2*(moment 1 qb:ℝ) := by
  have hC : (0:ℝ) ≤ (C:ℝ) := by norm_num [C, H, rhi, qb]
  have hq : (0:ℝ) ≤ (qb:ℝ) := by norm_num [qb]
  calc
    _ ≤ ∑ k ∈ range j, (C:ℝ)*(2*(j:ℝ))^2*((j-k:ℕ):ℝ)*(qb:ℝ)^(j-k) := by
      apply sum_le_sum
      intro k hk
      by_cases hx : k < 2 ∨ k = j
      · simp only [sineOffRow, if_pos hx]
        positivity
      · simp only [sineOffRow, if_neg hx]
        exact sine_lower_tail j k (mem_range.mp hk)
    _ = (C:ℝ)*(2*(j:ℝ))^2*(∑ k ∈ range j, ((j-k:ℕ):ℝ)*(qb:ℝ)^(j-k)) := by
      simp only [mul_sum, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (unit_lower_geometric_sum_bound j) (by positivity)

theorem sine_high_row_quartic_bound (j : ℕ) (hj : 2 ≤ j) :
    Summable (sineOffRow j) ∧
    sineMatrixEntry thetaParameter nome j j + ∑' k : ℕ, sineOffRow j k ≤
      HighFrequency.realValue (HighFrequency.singlePeriod 1) (2*(j:ℝ)) := by
  have he : (fun n : ℕ => sineOffRow j (n+(j+1))) =
      (fun n : ℕ => |sineMatrixEntry thetaParameter nome j (j+(n+1))|) := by
    funext n
    rw [show j+(n+1) = n+(j+1) by omega]
    simp only [sineOffRow, if_neg (by omega : ¬(n+(j+1) < 2 ∨ n+(j+1) = j))]
  have ht := sine_tail_bound j 1 (by omega)
  rw [← he] at ht
  have hs : Summable (sineOffRow j) := (summable_nat_add_iff (j+1)).mp ht.1
  refine ⟨hs, ?_⟩
  have hd : sineOffRow j j = 0 := by simp [sineOffRow]
  have hsplit : (∑' k : ℕ, sineOffRow j k) =
      (∑ k ∈ range j, sineOffRow j k)+(∑' n : ℕ, sineOffRow j (n+(j+1))) := by
    rw [← hs.sum_add_tsum_nat_add (j+1), sum_range_succ, hd, add_zero]
  have htval : (entryTailBound j 1:ℝ) =
      (C:ℝ)*((2*(j:ℝ))^2*(moment 1 qb:ℝ)+
        2*(2*(j:ℝ))*(moment 2 qb:ℝ)+(moment 3 qb:ℝ)) := by
    simp only [entryTailBound, unit_tail_one_values.1, unit_tail_one_values.2.1,
      unit_tail_one_values.2.2, Rat.cast_mul, Rat.cast_add, Rat.cast_pow,
      Rat.cast_ofNat, Rat.cast_natCast]
  rw [htval] at ht
  calc
    _ ≤ (-4*(rlo:ℝ)^2*(2*(j:ℝ))^4+45*(rhi:ℝ)*(2*(j:ℝ))^2)+
        ((C:ℝ)*(2*(j:ℝ))^2*(moment 1 qb:ℝ)+
          (C:ℝ)*((2*(j:ℝ))^2*(moment 1 qb:ℝ)+
          2*(2*(j:ℝ))*(moment 2 qb:ℝ)+(moment 3 qb:ℝ))) := by
      rw [hsplit]
      exact add_le_add (sine_diagonal_high_bound j (by omega))
        (add_le_add (sine_lower_sum_bound j) ht.2)
    _ = _ := by
      simp only [HighFrequency.realValue, HighFrequency.singlePeriod, shiftedQuartic,
        div_one, mul_one, Rat.cast_mul, Rat.cast_add, Rat.cast_pow, Rat.cast_ofNat,
        Rat.cast_zero, sub_zero]
      ring

theorem sine_all_tail_rows_dissipative (j : ℕ) (hj : 2 ≤ j) :
    Summable (sineOffRow j) ∧
    sineMatrixEntry thetaParameter nome j j + ∑' k : ℕ, sineOffRow j k < -100 := by
  by_cases hsmall : j < 4
  · rcases (show j = 2 ∨ j = 3 by omega) with rfl | rfl
    · have h := sine_low_row_bound 2 (by omega) (by omega)
      have hc : (sineFiniteRow 2:ℝ) < -120 := by exact_mod_cast sine_low_row_certificates.1
      exact ⟨h.1, h.2.trans_lt (hc.trans (by norm_num))⟩
    · have h := sine_low_row_bound 3 (by omega) (by omega)
      have hc : (sineFiniteRow 3:ℝ) < -1560 := by exact_mod_cast sine_low_row_certificates.2
      exact ⟨h.1, h.2.trans_lt (hc.trans (by norm_num))⟩
  · have h := sine_high_row_quartic_bound j hj
    have hj' : (4:ℝ) ≤ (j:ℝ) := by exact_mod_cast (show 4 ≤ j by omega)
    have hh := HighFrequency.sine_high_bound (2*(j:ℝ)) (by linarith)
    exact ⟨h.1, h.2.trans_lt (hh.trans (by norm_num))⟩

end Lemniscate.CoarseArithmetic
