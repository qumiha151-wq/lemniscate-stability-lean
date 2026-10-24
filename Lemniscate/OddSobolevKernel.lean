import Lemniscate.OddSobolevEntries

/-! The Sobolev distance kernel has an absolutely convergent complete integer
row, uniformly bounded by 512. Both frequency directions and zero are included. -/
namespace Lemniscate.OddArithmetic
open CoarseArithmetic

theorem odd_sobolev_positive_hasSum :
    HasSum (fun k : ℕ => oddSobolevKernel (k+1))
      ((60*(rhi:ℝ)*(H:ℝ))*(moment 1 qb:ℝ)) := by
  have hq : ‖(qb:ℝ)‖ < 1 := by norm_num [qb]
  have ht : tail1 qb 1 = moment 1 qb := by decide +kernel
  convert! (tail1_sound qb hq 1).mul_left (60*(rhi:ℝ)*(H:ℝ)) using 1
  · ext k
    simp only [oddSobolevKernel, if_neg (by omega : k+1 ≠ 0)]
    ring
  · rw [ht]

theorem odd_sobolev_nat_hasSum :
    HasSum oddSobolevKernel (256+(60*(rhi:ℝ)*(H:ℝ))*(moment 1 qb:ℝ)) := by
  have ht := (hasSum_nat_add_iff 1).mp odd_sobolev_positive_hasSum
  simpa only [Finset.sum_range_one, oddSobolevKernel, ite_true, add_comm] using ht

theorem odd_sobolev_integer_hasSum :
    HasSum (fun k : ℤ => oddSobolevKernel k.natAbs)
      (256+2*((60*(rhi:ℝ)*(H:ℝ))*(moment 1 qb:ℝ))) := by
  have hp : HasSum (fun k : ℕ => oddSobolevKernel (k:ℤ).natAbs)
      (256+(60*(rhi:ℝ)*(H:ℝ))*(moment 1 qb:ℝ)) := by
    simpa only [Int.natAbs_natCast] using odd_sobolev_nat_hasSum
  have hn : HasSum (fun k : ℕ => oddSobolevKernel (-((k:ℤ)+1)).natAbs)
      ((60*(rhi:ℝ)*(H:ℝ))*(moment 1 qb:ℝ)) := by
    have he (k : ℕ) : (-((k:ℤ)+1)).natAbs = k+1 := by
      rw [Int.natAbs_neg, ← Int.natCast_one, ← Int.natCast_add, Int.natAbs_natCast]
    simpa only [he] using odd_sobolev_positive_hasSum
  have ht := HasSum.of_nat_of_neg_add_one
    (f := fun k : ℤ => oddSobolevKernel k.natAbs) hp hn
  convert! ht using 1 <;> ring

theorem odd_sobolev_kernel_row_hasSum (i : ℤ) :
    HasSum (fun k : ℤ => oddSobolevKernel (i-k).natAbs)
      (256+2*((60*(rhi:ℝ)*(H:ℝ))*(moment 1 qb:ℝ))) := by
  have ht := (Equiv.subLeft i).hasSum_iff.mpr odd_sobolev_integer_hasSum
  simpa only [Function.comp_def, Equiv.subLeft_apply] using ht

theorem odd_sobolev_kernel_row_bound (i : ℤ) :
    Summable (fun k : ℤ => oddSobolevKernel (i-k).natAbs) ∧
      (∑' k : ℤ, oddSobolevKernel (i-k).natAbs) ≤ 512 := by
  have ht := odd_sobolev_kernel_row_hasSum i
  refine ⟨ht.summable, ?_⟩
  rw [ht.tsum_eq]
  norm_num [rhi, H, qb, moment]

theorem odd_sobolev_kernel_finite_row_bound (I : Finset ℤ) (i : ℤ) :
    (∑ k ∈ I, oddSobolevKernel (i-k).natAbs) ≤ 512 := by
  have ht := odd_sobolev_kernel_row_bound i
  exact (Summable.sum_le_tsum I (fun k _ => odd_sobolev_kernel_nonneg _) ht.1).trans ht.2

theorem odd_sobolev_kernel_symmetric (i j : ℤ) :
    oddSobolevKernel (i-j).natAbs = oddSobolevKernel (j-i).natAbs := by
  rw [show i-j = -(j-i) by omega, Int.natAbs_neg]

end Lemniscate.OddArithmetic
