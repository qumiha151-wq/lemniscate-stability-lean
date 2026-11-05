import Lemniscate.ShortSchurMatrices
import Lemniscate.ShortFourierEnclosure

/-! Analytic bounds for all omitted Fourier entries.  The small integer 32
is uniform in the outside frequency; no truncated matrix is used here. -/
namespace Lemniscate
open CoarseArithmetic

private theorem short_outer_polynomial_bounds (n m r : ℝ)
    (hr : |r| ≤ 3/4) (hm : 30 ≤ |m|) (hn : |n| ≤ |m|/2) :
    |(15/2:ℝ)*r*n*(7*m-n)| ≤ 32*m^2 ∧
    |(15/2:ℝ)*r*m*(7*n-m)| ≤ 32*m^2 ∧
    |r*((75/2:ℝ)*n+(105/2:ℝ)*m)| ≤ 32*m^2 ∧
    |r*((75/2:ℝ)*m+(105/2:ℝ)*n)| ≤ 32*m^2 ∧
    |45*r| ≤ 32*m^2 := by
  have hm0 := abs_nonneg m
  have hs : |m|^2 = m^2 := sq_abs m
  have h0 : |(15/2:ℝ)*r*n*(7*m-n)| ≤
      (15/2:ℝ)*(3/4)*(|m|/2)*(7*|m|+|m|/2) := by
    calc
      _ ≤ (15/2:ℝ)*|r| *|n| *(7*|m|+|n|) := by
        norm_num only [abs_mul, abs_div, abs_of_pos (by norm_num : (0:ℝ)<15), abs_of_pos (by norm_num : (0:ℝ)<2)]
        gcongr
        simpa [abs_mul] using abs_sub (7*m) n
      _ ≤ _ := by gcongr
  have h1 : |(15/2:ℝ)*r*m*(7*n-m)| ≤
      (15/2:ℝ)*(3/4)*|m| *(7*(|m|/2)+|m|) := by
    calc
      _ ≤ (15/2:ℝ)*|r| *|m| *(7*|n|+|m|) := by
        norm_num only [abs_mul, abs_div, abs_of_pos (by norm_num : (0:ℝ)<15), abs_of_pos (by norm_num : (0:ℝ)<2)]
        gcongr
        simpa [abs_mul] using abs_sub (7*n) m
      _ ≤ _ := by gcongr
  have h2 : |r*((75/2:ℝ)*n+(105/2:ℝ)*m)| ≤
      (3/4:ℝ)*((75/2)*(|m|/2)+(105/2)*|m|) := by
    calc
      _ ≤ |r| *((75/2:ℝ)*|n|+(105/2:ℝ)*|m|) := by
        rw [abs_mul]
        gcongr
        simpa [abs_mul, abs_div] using
          abs_add_le ((75/2:ℝ)*n) ((105/2:ℝ)*m)
      _ ≤ _ := by gcongr
  have h3 : |r*((75/2:ℝ)*m+(105/2:ℝ)*n)| ≤
      (3/4:ℝ)*((75/2)*|m|+(105/2)*(|m|/2)) := by
    calc
      _ ≤ |r| *((75/2:ℝ)*|m|+(105/2:ℝ)*|n|) := by
        rw [abs_mul]
        gcongr
        simpa [abs_mul, abs_div] using
          abs_add_le ((75/2:ℝ)*m) ((105/2:ℝ)*n)
      _ ≤ _ := by gcongr
  have h4 : |45*r| ≤ (45:ℝ)*(3/4) := by
    simpa [abs_mul] using mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ) ≤ 45)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg (|m|-30)]

theorem short_bloch_outside_bound (r : ℝ) (h : ℕ → ℝ) (k : Fin 5)
    (n m : ℤ) (B : ℝ) (hr : |r| ≤ 3/4)
    (hn : |(n:ℝ)| ≤ 14) (hm : 30 ≤ |(m:ℝ)|)
    (hB : |h ((n-m).natAbs/2)| ≤ B) :
    |shortBlochEntry r h k n m| ≤ 32*(m:ℝ)^2*B ∧
    |shortBlochEntry r h k m n| ≤ 32*(m:ℝ)^2*B := by
  have hne : n ≠ m := by
    intro he
    subst m
    linarith
  have hnm : |(n:ℝ)| ≤ |(m:ℝ)|/2 := by linarith
  have hp := short_outer_polynomial_bounds (n:ℝ) (m:ℝ) r hr hm hnm
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  have hrev : (m-n).natAbs = (n-m).natAbs := by
    rw [← Int.natAbs_neg (n-m), neg_sub]
  have hb (a : ℝ) (ha : |a| ≤ 32*(m:ℝ)^2) :
      |a*h ((n-m).natAbs/2)| ≤ 32*(m:ℝ)^2*B := by
    rw [abs_mul]
    exact mul_le_mul ha hB (abs_nonneg _) (by positivity)
  fin_cases k <;>
    simp only [shortBlochEntry, hne, Ne.symm hne, if_false,
      sub_zero, hrev] <;>
    constructor
  · exact hb _ hp.1
  · exact hb _ hp.2.1
  · exact hb _ hp.2.2.1
  · exact hb _ hp.2.2.2.1
  · exact hb _ hp.2.2.2.2
  · exact hb _ hp.2.2.2.2
  all_goals simpa using mul_nonneg (by positivity : (0:ℝ) ≤ 32*(m:ℝ)^2) hB0

theorem short_outside_coefficient_bound (n m : ℤ) (l : ℕ)
    (hn : n.natAbs ≤ 14) (hm : m.natAbs = 2*l) (hl : 15 ≤ l) :
    |fourierCoefficient lemniscateFrequencySquared nome ((n-m).natAbs/2)| ≤
      (H:ℝ)*((l:ℝ)+7)*(qb:ℝ)^(l-7) := by
  have ht := Int.natAbs_add_le (m-n) n
  rw [sub_add_cancel, hm] at ht
  have hrev : (m-n).natAbs = (n-m).natAbs := by
    rw [← Int.natAbs_neg (n-m), neg_sub]
  rw [hrev] at ht
  have hindex : l-7 ≤ (n-m).natAbs/2 := by omega
  have hsmall : 0 < l-7 := by omega
  have hmajor := common_index_coefficient_majorant (l-7)
    ((n-m).natAbs/2) hsmall hindex
  have hle : ((l-7:ℕ):ℝ) ≤ (l:ℝ)+7 := by
    have h := Nat.sub_le l 7
    have hc : ((l-7:ℕ):ℝ) ≤ (l:ℝ) := by exact_mod_cast h
    linarith
  apply hmajor.trans
  calc
    _ = (H:ℝ)*((l-7:ℕ):ℝ)*(qb:ℝ)^(l-7) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hle (by norm_num [H,rhi,qb]))
      (pow_nonneg (by norm_num [qb]) _)

/-- The genuine coefficient sequence, including every outside frequency. -/
theorem short_actual_bloch_outside_bound (k : Fin 5) (n m : ℤ) (l : ℕ)
    (hn : n.natAbs ≤ 14) (hm : m.natAbs = 2*l) (hl : 15 ≤ l) :
    |shortBlochEntry lemniscateFrequencySquared
        (fourierCoefficient lemniscateFrequencySquared nome) k n m| ≤
      32*(m:ℝ)^2*((H:ℝ)*((l:ℝ)+7)*(qb:ℝ)^(l-7)) ∧
    |shortBlochEntry lemniscateFrequencySquared
        (fourierCoefficient lemniscateFrequencySquared nome) k m n| ≤
      32*(m:ℝ)^2*((H:ℝ)*((l:ℝ)+7)*(qb:ℝ)^(l-7)) := by
  have hr := short_frequency_enclosure
  have hr' : |lemniscateFrequencySquared| ≤ 3/4 := by
    rw [abs_le]
    norm_num [Contains,shortFrequencyInterval] at hr
    constructor <;> linarith
  have hn' : |(n:ℝ)| ≤ 14 := by
    have hc : (n.natAbs:ℝ) ≤ 14 := by exact_mod_cast hn
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hc
  have hm' : 30 ≤ |(m:ℝ)| := by
    have hc : 30 ≤ (m.natAbs:ℝ) := by exact_mod_cast (show 30 ≤ m.natAbs by omega)
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hc
  exact short_bloch_outside_bound _ _ k n m _ hr' hn' hm'
    (short_outside_coefficient_bound n m l hn hm hl)

end Lemniscate
