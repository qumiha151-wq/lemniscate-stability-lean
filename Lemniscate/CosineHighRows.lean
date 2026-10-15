import Lemniscate.CosineHighEntries
import Mathlib.Algebra.BigOperators.Intervals

/-! Complete high rows are bounded by the paper's actual quartic, using the
lower finite part and the entire upper tail. This then joins the nine low rows. -/
namespace Lemniscate.CoarseArithmetic
open Finset

set_option maxRecDepth 100000 in
theorem tail_one_values :
    tail1 (qb/a) 1 = moment 1 (qb/a) ∧
    tail1 (qb*a) 1 = moment 1 (qb*a) ∧
    tail2 (qb*a) 1 = moment 2 (qb*a) ∧
    tail3 (qb*a) 1 = moment 3 (qb*a) := by decide +kernel

theorem lower_geometric_sum_bound (j : ℕ) :
    (∑ k ∈ range j, ((j-k:ℕ):ℝ)*((qb/a:ℚ):ℝ)^(j-k)) ≤ (moment 1 (qb/a):ℝ) := by
  have hz : ‖((qb/a:ℚ):ℝ)‖ < 1 := by norm_num [qb, a]
  have hz0 : (0:ℝ) ≤ ((qb/a:ℚ):ℝ) := by norm_num [qb, a]
  have ht : HasSum (fun k : ℕ => ((k+1:ℕ):ℝ)*((qb/a:ℚ):ℝ)^(k+1))
      (moment 1 (qb/a):ℝ) := by
    simpa only [tail_one_values.1] using tail1_sound (qb/a) hz 1
  calc
    _ = ∑ k ∈ range j, ((j-1-k+1:ℕ):ℝ)*((qb/a:ℚ):ℝ)^(j-1-k+1) := by
      apply sum_congr rfl
      intro k hk
      have he : j-k = j-1-k+1 := by have := mem_range.mp hk; omega
      rw [he]
    _ = ∑ k ∈ range j, ((k+1:ℕ):ℝ)*((qb/a:ℚ):ℝ)^(k+1) :=
      sum_range_reflect (fun k => ((k+1:ℕ):ℝ)*((qb/a:ℚ):ℝ)^(k+1)) j
    _ ≤ _ := sum_le_hasSum (range j) (fun k _ => by positivity) ht

theorem cosine_lower_sum_bound (j : ℕ) (hj : 3 ≤ j) :
    (∑ k ∈ range j, cosineOffRow j k) ≤
      (C:ℝ)*(2*(j:ℝ))^2*(moment 1 (qb/a):ℝ) := by
  have hC : (0:ℝ) ≤ (C:ℝ) := by norm_num [C, H, rhi, qb]
  calc
    _ ≤ ∑ k ∈ range j, (C:ℝ)*(2*(j:ℝ))^2*((j-k:ℕ):ℝ)*((qb/a:ℚ):ℝ)^(j-k) :=
      sum_le_sum (fun k hk => cosine_weighted_lower_majorant j k hj (mem_range.mp hk))
    _ = (C:ℝ)*(2*(j:ℝ))^2*
        (∑ k ∈ range j, ((j-k:ℕ):ℝ)*((qb/a:ℚ):ℝ)^(j-k)) := by
      simp only [mul_sum, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (lower_geometric_sum_bound j) (by positivity)

theorem weighted_tail_one (j : ℕ) (hj : 3 ≤ j) :
    (weightedEntryTailBound j 1:ℝ) =
      (C:ℝ)*((2*(j:ℝ))^2*(moment 1 (qb*a):ℝ)+
        2*(2*(j:ℝ))*(moment 2 (qb*a):ℝ)+(moment 3 (qb*a):ℝ)) := by
  simp only [weightedEntryTailBound, tailWeightFactor_eq_one j hj, mul_one,
    tail_one_values.2.1, tail_one_values.2.2.1, tail_one_values.2.2.2,
    Rat.cast_mul, Rat.cast_add, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast]

theorem cosine_high_row_quartic_bound (j : ℕ) (hj : 3 ≤ j) :
    Summable (cosineOffRow j) ∧
    cosineMatrixEntry thetaParameter nome j j + ∑' k : ℕ, cosineOffRow j k ≤
      HighFrequency.realValue (HighFrequency.singlePeriod a) (2*(j:ℝ)) := by
  have heq : (fun n : ℕ => cosineOffRow j (n+(j+1))) =
      (fun n : ℕ => |cosineMatrixEntry thetaParameter nome j (j+(n+1))| *
        ((weight (j+(n+1)):ℝ)/(weight j:ℝ))) := by
    funext n
    rw [show j+(n+1) = n+(j+1) by omega]
    simp only [cosineOffRow, if_neg (show n+(j+1) ≠ j by omega)]
  have ht := cosine_weighted_tail_bound j 1 (by norm_num) (by omega)
  rw [← heq] at ht
  have hs : Summable (cosineOffRow j) := (summable_nat_add_iff (j+1)).mp ht.1
  refine ⟨hs, ?_⟩
  have hdiag : cosineOffRow j j = 0 := by simp [cosineOffRow]
  have hsplit : (∑' k : ℕ, cosineOffRow j k) =
      (∑ k ∈ range j, cosineOffRow j k)+(∑' n : ℕ, cosineOffRow j (n+(j+1))) := by
    rw [← hs.sum_add_tsum_nat_add (j+1), sum_range_succ, hdiag, add_zero]
  rw [weighted_tail_one j hj] at ht
  calc
    _ ≤ (-4*(rlo:ℝ)^2*(2*(j:ℝ))^4+45*(rhi:ℝ)*(2*(j:ℝ))^2)+
        ((C:ℝ)*(2*(j:ℝ))^2*(moment 1 (qb/a):ℝ)+
        (C:ℝ)*((2*(j:ℝ))^2*(moment 1 (qb*a):ℝ)+
          2*(2*(j:ℝ))*(moment 2 (qb*a):ℝ)+(moment 3 (qb*a):ℝ))) := by
      rw [hsplit]
      exact add_le_add (cosine_diagonal_high_bound j (by omega))
        (add_le_add (cosine_lower_sum_bound j hj) ht.2)
    _ = _ := by
      simp only [HighFrequency.realValue, HighFrequency.singlePeriod, shiftedQuartic,
        Rat.cast_mul, Rat.cast_add, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_zero,
        sub_zero]
      ring

theorem cosine_high_rows_dissipative (j : ℕ) (hj : 9 ≤ j) :
    Summable (cosineOffRow j) ∧
    cosineMatrixEntry thetaParameter nome j j + ∑' k : ℕ, cosineOffRow j k < -8000 := by
  have h := cosine_high_row_quartic_bound j (by omega)
  refine ⟨h.1, h.2.trans_lt (HighFrequency.cosine_high_bound _ ?_)⟩
  have hj' : (9:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  linarith

theorem cosine_all_rows_dissipative (j : ℕ) :
    Summable (cosineOffRow j) ∧
    cosineMatrixEntry thetaParameter nome j j + ∑' k : ℕ, cosineOffRow j k < -(21/4:ℝ) := by
  by_cases hj : j < 9
  · exact cosine_low_rows_dissipative ⟨j, hj⟩
  · have h := cosine_high_rows_dissipative j (by omega)
    exact ⟨h.1, h.2.trans (by norm_num)⟩

end Lemniscate.CoarseArithmetic
