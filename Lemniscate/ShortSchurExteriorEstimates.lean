import Lemniscate.ShortSchurOuterBounds
import Lemniscate.ShortSchurFiniteCertificate
import Lemniscate.ShortSchurRawBounds

/-! Bounds for the genuine exterior entries, after the Sobolev weights.
The finite-rank correction is supported in the fifteen-mode head. -/
namespace Lemniscate.CoarseArithmetic
open Finset Matrix

theorem short_head_index_none_of_eight_le (n : ℤ) (hn : 8 ≤ n.natAbs) :
    shortHeadIndex n = none := by
  unfold shortHeadIndex
  rw [dif_neg (by omega)]

theorem short_half_square_pos (n : ℤ) (hn : 1 ≤ n.natAbs) :
    0 < (2*(n:ℝ))^2 := by
  have hn0 : n ≠ 0 := by omega
  exact sq_pos_of_ne_zero (mul_ne_zero (by norm_num) (Int.cast_ne_zero.mpr hn0))

theorem short_half_square_one_le (n : ℤ) (hn : 1 ≤ n.natAbs) :
    1 ≤ (2*(n:ℝ))^2 := by
  have hn0 : n ≠ 0 := by omega
  have hsq : (1:ℤ) ≤ n^2 := by have hs := sq_pos_of_ne_zero hn0; omega
  have hcast : (1:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast hsq
  nlinarith

theorem short_high_entry_symmetric (j : Fin 5) (n m : ℤ) :
    shortHighEntry j n m = shortHighEntry j m n := by
  unfold shortHighEntry
  rw [short_bernstein_kernel_symmetric, mul_comm]

theorem short_high_entry_raw (j : Fin 5) (n m : ℤ)
    (hn : 8 ≤ n.natAbs) (hm : 8 ≤ m.natAbs) :
    shortHighEntry j n m =
      shortRawBernsteinEntry lemniscateFrequencySquared shortActualCoefficient j n m /
        ((2*(n:ℝ))^2*(2*(m:ℝ))^2) := by
  simp only [shortHighEntry, shortBernsteinKernel,
    short_head_index_none_of_eight_le n hn, short_head_index_none_of_eight_le m hm]

theorem short_cross_outside_bound (j : Fin 5) (i : Fin 7) (m : ℤ)
    (hm : 15 ≤ m.natAbs) :
    |shortCrossEntry j i m| ≤ 10^6*shortOutsideEnvelope m.natAbs := by
  have hE := short_outside_envelope_nonneg m.natAbs
  have hden := short_half_square_pos m (by omega)
  have hcolumn (a : Fin 15) :
      |shortBernsteinKernel lemniscateFrequencySquared shortActualCoefficient j
        ((a.val:ℤ)-7) m| ≤ 22400*(2*(m:ℝ))^2*shortOutsideEnvelope m.natAbs := by
    simp only [shortBernsteinKernel, short_head_index_half,
      short_head_index_none_of_eight_le m (by omega)]
    exact short_outside_bernstein_bound j a m m.natAbs rfl hm
  have hs := short_abs_sum_product_bound _ _ 2
    (22400*(2*(m:ℝ))^2*shortOutsideEnvelope m.natAbs)
    (short_f_column_l1_bound i) hcolumn (by positivity)
  unfold shortCrossEntry
  rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
  exact hs.trans (by nlinarith)

theorem short_high_head_outside_bound (j : Fin 5) (n m : ℤ)
    (hn : 1 ≤ n.natAbs) (hn7 : n.natAbs ≤ 7) (hm : 15 ≤ m.natAbs) :
    |shortHighEntry j n m| ≤ 10^6*shortOutsideEnvelope m.natAbs := by
  have hd := short_half_square_pos m (by omega)
  have hd' := short_half_square_one_le n hn
  have hE := short_outside_envelope_nonneg m.natAbs
  have hhead : ∃ a, shortHeadIndex n = some a := by
    unfold shortHeadIndex
    rw [dif_pos (by omega)]
    exact ⟨_,rfl⟩
  obtain ⟨a,ha⟩ := hhead
  have hh := short_outside_bernstein_bound j a m m.natAbs rfl hm
  unfold shortHighEntry
  simp only [shortBernsteinKernel, ha,
    short_head_index_none_of_eight_le m (by omega)]
  rw [abs_div, abs_of_pos (mul_pos (by linarith) hd), div_le_iff₀ (mul_pos (by linarith) hd)]
  exact hh.trans (by
    have hmul := mul_le_mul_of_nonneg_right hd' (mul_nonneg hd.le hE)
    nlinarith)

theorem short_high_raw_off_diagonal_bound (j : Fin 5) (n m : ℤ)
    (hnm : n ≠ m) (hn : 4 ≤ n.natAbs) (hm : 4 ≤ m.natAbs) :
    |shortRawBernsteinEntry lemniscateFrequencySquared shortActualCoefficient j n m /
        ((2*(n:ℝ))^2*(2*(m:ℝ))^2)| ≤
      (shortHighOffCoefficient:ℝ)*((n-m).natAbs:ℝ)*(qb:ℝ)^(n-m).natAbs := by
  have hden := mul_pos (short_half_square_pos n (by omega))
    (short_half_square_pos m (by omega))
  have hh := short_actual_raw_off_diagonal_bound j n m hnm hn hm
  rw [show shortActualCoefficient = fourierCoefficient lemniscateFrequencySquared nome from rfl]
  rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
  exact hh.trans_eq (by ring)

theorem short_outside_envelope_max (l : ℕ) (hl : 15 ≤ l) :
    shortOutsideEnvelope l ≤ 22*(H:ℝ)*(qb:ℝ)^8 := by
  have hq : (0:ℝ) ≤ (qb:ℝ) := by norm_num [qb]
  have hH : (0:ℝ) ≤ (H:ℝ) := by norm_num [H,rhi,qb]
  have ht := nat_mul_geometric_antitone (qb:ℝ) hq (by norm_num [qb]) 8 (l-7)
    (by omega) (by omega)
  have hc : (l:ℝ)+7 ≤ (11/4:ℝ)*((l-7:ℕ):ℝ) := by
    have hn : ((l-7:ℕ):ℝ) = (l:ℝ)-7 := by rw [Nat.cast_sub (by omega)]; norm_num
    rw [hn]
    have hl' : (15:ℝ) ≤ (l:ℝ) := by exact_mod_cast hl
    linarith
  unfold shortOutsideEnvelope
  calc
    _ ≤ (H:ℝ)*((11/4:ℝ)*((l-7:ℕ):ℝ))*(qb:ℝ)^(l-7) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hH) (pow_nonneg hq _)
    _ = (H:ℝ)*(11/4)*(((l-7:ℕ):ℝ)*(qb:ℝ)^(l-7)) := by ring
    _ ≤ (H:ℝ)*(11/4)*(8*(qb:ℝ)^8) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by ring

end Lemniscate.CoarseArithmetic
