import Lemniscate.EntryMajorant

/-! Absolute convergence and explicit rational bounds for complete upper row
tails of the coefficient-defined matrices. No finite truncation is substituted
for the infinite series. The differential-operator identification is separate. -/
namespace Lemniscate.CoarseArithmetic

def entryTailBound (j L : ℕ) : ℚ :=
  C*((2*(j:ℚ))^2*tail1 qb L+2*(2*(j:ℚ))*tail2 qb L+tail3 qb L)

theorem hasSum_entry_majorant (j L : ℕ) :
    HasSum (fun a : ℕ =>
      (C:ℝ)*(2*(j:ℝ)+((a+L:ℕ):ℝ))^2*((a+L:ℕ):ℝ)*(qb:ℝ)^(a+L))
      (entryTailBound j L : ℝ) := by
  have hq : ‖(qb:ℝ)‖ < 1 := by norm_num [qb]
  convert! ((((tail1_sound qb hq L).mul_left ((2*(j:ℝ))^2)).add
    ((tail2_sound qb hq L).mul_left (2*(2*(j:ℝ))))).add
    (tail3_sound qb hq L)).mul_left (C:ℝ) using 1
  · ext a
    ring
  · simp only [entryTailBound, Rat.cast_mul, Rat.cast_add, Rat.cast_pow,
      Rat.cast_ofNat, Rat.cast_natCast]

theorem positive_frequency_tail_bound (ε : ℝ) (j L : ℕ)
    (hε : |ε| ≤ 1) (hL : 0 < L) :
    Summable (fun a : ℕ =>
      |positiveFrequencyEntry thetaParameter nome ε j (j+(a+L))|) ∧
    (∑' a : ℕ, |positiveFrequencyEntry thetaParameter nome ε j (j+(a+L))|) ≤
      (entryTailBound j L : ℝ) := by
  have hm (a : ℕ) :
      |positiveFrequencyEntry thetaParameter nome ε j (j+(a+L))| ≤
      (C:ℝ)*(2*(j:ℝ)+((a+L:ℕ):ℝ))^2*((a+L:ℕ):ℝ)*(qb:ℝ)^(a+L) := by
    simpa only [Nat.add_sub_cancel_left] using
      positive_frequency_upper_tail ε j (j+(a+L)) hε (by omega)
  have hs := Summable.of_nonneg_of_le (fun a => abs_nonneg _) hm
    (hasSum_entry_majorant j L).summable
  refine ⟨hs, ?_⟩
  simpa only [(hasSum_entry_majorant j L).tsum_eq] using
    hs.tsum_le_tsum hm (hasSum_entry_majorant j L).summable

theorem cosine_tail_bound (j L : ℕ) (hj : 0 < j) (hL : 0 < L) :
    Summable (fun a : ℕ =>
      |cosineMatrixEntry thetaParameter nome j (j+(a+L))|) ∧
    (∑' a : ℕ, |cosineMatrixEntry thetaParameter nome j (j+(a+L))|) ≤
      (entryTailBound j L : ℝ) := by
  have hm (a : ℕ) :
      |cosineMatrixEntry thetaParameter nome j (j+(a+L))| ≤
      (C:ℝ)*(2*(j:ℝ)+((a+L:ℕ):ℝ))^2*((a+L:ℕ):ℝ)*(qb:ℝ)^(a+L) := by
    simpa only [Nat.add_sub_cancel_left] using
      cosine_upper_tail j (j+(a+L)) hj (by omega)
  have hs := Summable.of_nonneg_of_le (fun a => abs_nonneg _) hm
    (hasSum_entry_majorant j L).summable
  refine ⟨hs, ?_⟩
  simpa only [(hasSum_entry_majorant j L).tsum_eq] using
    hs.tsum_le_tsum hm (hasSum_entry_majorant j L).summable

end Lemniscate.CoarseArithmetic
