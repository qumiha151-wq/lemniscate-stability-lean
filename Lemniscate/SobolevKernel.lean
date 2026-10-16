import Lemniscate.SobolevEntryBounds

/-! The distance kernel controlling the H2 form has a uniformly bounded
complete row sum. Both sides of every row and the diagonal are included. -/
namespace Lemniscate.CoarseArithmetic
open Finset

theorem kernel_positive_hasSum :
    HasSum (fun n : ℕ => cosineKernel (n+1)) (2*(C:ℝ)*(moment 1 qb:ℝ)) := by
  have ht : tail1 qb 1 = moment 1 qb := by decide +kernel
  have hq : ‖(qb:ℝ)‖ < 1 := by norm_num [qb]
  convert! (tail1_sound qb hq 1).mul_left (2*(C:ℝ)) using 1
  · ext n
    simp only [cosineKernel, if_neg (by omega : n+1 ≠ 0)]
    ring
  · rw [ht]

theorem kernel_lower_sum_bound (j : ℕ) :
    (∑ k ∈ range j, cosineKernel (j-k+(k-j))) ≤ 2*(C:ℝ)*(moment 1 qb:ℝ) := by
  calc
    _ = ∑ k ∈ range j, cosineKernel (j-1-k+1) := by
      apply sum_congr rfl
      intro k hk
      congr 1
      have := mem_range.mp hk
      omega
    _ = ∑ k ∈ range j, cosineKernel (k+1) :=
      sum_range_reflect (fun k => cosineKernel (k+1)) j
    _ ≤ _ := sum_le_hasSum (range j) (fun k _ => cosineKernel_nonneg (k+1))
      kernel_positive_hasSum

theorem cosine_kernel_row_bound (j : ℕ) :
    Summable (fun k : ℕ => cosineKernel (j-k+(k-j))) ∧
    (∑' k : ℕ, cosineKernel (j-k+(k-j))) ≤ 1024 := by
  have ht : HasSum (fun n : ℕ => cosineKernel (j-(n+(j+1))+(n+(j+1)-j)))
      (2*(C:ℝ)*(moment 1 qb:ℝ)) := by
    convert! kernel_positive_hasSum using 1
    ext n
    congr 1
    omega
  have hs : Summable (fun k : ℕ => cosineKernel (j-k+(k-j))) :=
    (summable_nat_add_iff (j+1)).mp ht.summable
  refine ⟨hs, ?_⟩
  have hd : cosineKernel (j-j+(j-j)) = 512 := by simp [cosineKernel]
  calc
    _ = ((∑ k ∈ range j, cosineKernel (j-k+(k-j)))+512)+
        (∑' n : ℕ, cosineKernel (j-(n+(j+1))+(n+(j+1)-j))) := by
      rw [← hs.sum_add_tsum_nat_add (j+1), sum_range_succ, hd]
    _ ≤ (2*(C:ℝ)*(moment 1 qb:ℝ)+512)+(2*(C:ℝ)*(moment 1 qb:ℝ)) := by
      rw [ht.tsum_eq]
      exact add_le_add (add_le_add (kernel_lower_sum_bound j) le_rfl) le_rfl
    _ ≤ _ := by norm_num [C, H, rhi, qb, moment]

theorem cosine_kernel_finite_row_bound (I : Finset ℕ) (j : ℕ) :
    (∑ k ∈ I, cosineKernel (j-k+(k-j))) ≤ 1024 := by
  have h := cosine_kernel_row_bound j
  exact (Summable.sum_le_tsum I (fun k _ => cosineKernel_nonneg _) h.1).trans h.2

end Lemniscate.CoarseArithmetic
