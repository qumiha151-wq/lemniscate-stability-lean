import Lemniscate.OddWeightedEntries
import Lemniscate.OddHighMoments

/-! Full normalized rows on each sign branch. Summability is deduced from the
entry estimates, and the opposite branch is strictly below 8*|n+alpha|^2. -/
namespace Lemniscate.OddArithmetic
open CoarseArithmetic

theorem odd_same_lower_sum_bound (s : ℤ) (hs : s = 1 ∨ s = -1) (j : ℕ) (hj : 3 ≤ j)
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    (∑ k ∈ Finset.range j, oddSignedRow α s j s k) ≤
      (45*(rhi:ℝ)*(H:ℝ))*|(oddSignedFrequency s j:ℝ)+α|^2*(moment 1 (qb/a):ℝ) := by
  have hE : 0 ≤ (45*(rhi:ℝ)*(H:ℝ)) := by norm_num [rhi, H, qb]
  calc
    _ ≤ ∑ k ∈ Finset.range j, (45*(rhi:ℝ)*(H:ℝ))*|(oddSignedFrequency s j:ℝ)+α|^2*
        ((j-k:ℕ):ℝ)*((qb/a:ℚ):ℝ)^(j-k) :=
      Finset.sum_le_sum (fun k hk => odd_same_lower_weighted_bound s hs j k hj
        (Finset.mem_range.mp hk) α hα hα')
    _ = ((45*(rhi:ℝ)*(H:ℝ))*|(oddSignedFrequency s j:ℝ)+α|^2)*
        (∑ k ∈ Finset.range j, ((j-k:ℕ):ℝ)*((qb/a:ℚ):ℝ)^(j-k)) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (lower_geometric_sum_bound j) (by positivity)

theorem odd_same_upper_tail_bound (s : ℤ) (hs : s = 1 ∨ s = -1) (j : ℕ) (hj : 3 ≤ j)
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    Summable (fun k : ℕ => oddSignedRow α s j s (j+(k+1))) ∧
    (∑' k : ℕ, oddSignedRow α s j s (j+(k+1))) ≤
      (45*(rhi:ℝ)*(H:ℝ))*(|(oddSignedFrequency s j:ℝ)+α|^2*(moment 1 (qb*a):ℝ)+
        2*|(oddSignedFrequency s j:ℝ)+α| * (moment 2 (qb*a):ℝ)+(moment 3 (qb*a):ℝ)/3) := by
  have hm (k : ℕ) := odd_same_upper_weighted_bound s hs j (j+(k+1)) hj (by omega) α hα hα'
  simp only [Nat.add_sub_cancel_left] at hm
  have hsum := odd_upper_majorant_hasSum |(oddSignedFrequency s j:ℝ)+α|
  have ha := Summable.of_nonneg_of_le (fun k => odd_signed_row_nonneg α hα hα' s s j _) hm hsum.summable
  exact ⟨ha, by simpa only [hsum.tsum_eq] using ha.tsum_le_tsum hm hsum.summable⟩

theorem odd_same_branch_sum_bound (s : ℤ) (hs : s = 1 ∨ s = -1) (j : ℕ) (hj : 3 ≤ j)
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    Summable (oddSignedRow α s j s) ∧
    (∑' k : ℕ, oddSignedRow α s j s k) ≤
      (45*(rhi:ℝ)*(H:ℝ))*(|(oddSignedFrequency s j:ℝ)+α|^2*
        ((moment 1 (qb/a):ℝ)+(moment 1 (qb*a):ℝ))+
        2*|(oddSignedFrequency s j:ℝ)+α| * (moment 2 (qb*a):ℝ)+(moment 3 (qb*a):ℝ)/3) := by
  have ht := odd_same_upper_tail_bound s hs j hj α hα hα'
  have heq : (fun k : ℕ => oddSignedRow α s j s (k+(j+1))) =
      (fun k : ℕ => oddSignedRow α s j s (j+(k+1))) := by
    funext k
    congr 1
    omega
  have ha : Summable (oddSignedRow α s j s) :=
    (summable_nat_add_iff (j+1)).mp (by rw [heq]; exact ht.1)
  refine ⟨ha, ?_⟩
  have hl := odd_same_lower_sum_bound s hs j hj α hα hα'
  rw [← ha.sum_add_tsum_nat_add (j+1), Finset.sum_range_succ, odd_signed_row_diagonal, add_zero, heq]
  nlinarith [ht.2]

theorem odd_cross_branch_sum_bound (s : ℤ) (hs : s = 1 ∨ s = -1) (j : ℕ) (hj : 6 ≤ j)
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    Summable (oddSignedRow α s j (-s)) ∧
    (∑' k : ℕ, oddSignedRow α s j (-s) k) < 8*|(oddSignedFrequency s j:ℝ)+α|^2 := by
  let v : ℝ := |(oddSignedFrequency s j:ℝ)+α|
  let c : ℝ := (45*(rhi:ℝ)*(H:ℝ))*(37/16)*(qb:ℝ)*((qb/a:ℚ):ℝ)^j
  have hf := odd_signed_shift_bounds s hs j α hα hα'
  have hjr : (6:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  have hv : 1 ≤ v := by dsimp only [v]; linarith [hf.1]
  have hvpos : 0 < v := by linarith
  have hc : 0 ≤ c := by
    have hE : 0 ≤ (45*(rhi:ℝ)*(H:ℝ)) := by norm_num [rhi, H, qb]
    have hq : 0 ≤ (qb:ℝ) := by norm_num [qb]
    have hz : 0 ≤ ((qb/a:ℚ):ℝ) := by norm_num [qb, a]
    dsimp only [c]
    positivity
  have ht : 0 ≤ ((qb*a:ℚ):ℝ) := by norm_num [qb, a]
  have hm (k : ℕ) : oddSignedRow α s j (-s) k ≤
      (c*v^3)*((4+8*(k:ℝ)+5*(k:ℝ)^2+(k:ℝ)^3)*((qb*a:ℚ):ℝ)^k) := by
    have hp := odd_cross_polynomial_bound v (k:ℝ) hv (Nat.cast_nonneg _)
    calc
      _ ≤ c*(v+(k:ℝ))*(2*v+(k:ℝ))^2*((qb*a:ℚ):ℝ)^k :=
        odd_cross_weighted_bound s hs j k (by omega) α hα hα'
      _ = (c*((qb*a:ℚ):ℝ)^k)*((v+(k:ℝ))*(2*v+(k:ℝ))^2) := by ring
      _ ≤ (c*((qb*a:ℚ):ℝ)^k)*(v^3*(4+8*(k:ℝ)+5*(k:ℝ)^2+(k:ℝ)^3)) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by ring
  have hsum := odd_cross_moment_hasSum.mul_left (c*v^3)
  have ha := Summable.of_nonneg_of_le (fun k => odd_signed_row_nonneg α hα hα' s (-s) j k)
    hm hsum.summable
  refine ⟨ha, ?_⟩
  have hb : (∑' k : ℕ, oddSignedRow α s j (-s) k) ≤ (c*v^3)*(oddCrossMoment:ℝ) := by
    simpa only [hsum.tsum_eq] using ha.tsum_le_tsum hm hsum.summable
  have hc8 : c*v*(oddCrossMoment:ℝ) < 8 := odd_cross_coefficient_bound j hj v hf.2
  have hstrict := mul_lt_mul_of_pos_right hc8 (sq_pos_of_pos hvpos)
  change (∑' k : ℕ, oddSignedRow α s j (-s) k) < 8*v^2
  nlinarith

end Lemniscate.OddArithmetic
