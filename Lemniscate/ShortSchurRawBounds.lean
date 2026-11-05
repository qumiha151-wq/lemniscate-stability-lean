import Lemniscate.ShortSchurKernel
import Lemniscate.ShortSchurTailBounds
import Lemniscate.ShortSchurHighData

namespace Lemniscate
open CoarseArithmetic Finset

private theorem short_high_weight_bounds (a b : ℝ) (ha : 8 ≤ a) (hb : 8 ≤ b) :
    (a+1/2)*(b+1/2) ≤ ((17/16:ℝ)^2/64)*a^2*b^2 ∧
    (a+b)^2 ≤ (1/4:ℝ)^2*a^2*b^2 := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hab : 64 ≤ a*b := by nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  have hp : a*b ≤ a^2*b^2/64 := by
    nlinarith [mul_nonneg (mul_nonneg ha0 hb0) (sub_nonneg.mpr hab)]
  have hs : a+b ≤ a*b/4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  have hs2 : (a+b)^2 ≤ (a*b/4)^2 := by
    exact pow_le_pow_left₀ (by positivity) hs 2
  constructor
  · have ha' : a+1/2 ≤ (17/16:ℝ)*a := by linarith
    have hb' : b+1/2 ≤ (17/16:ℝ)*b := by linarith
    have ht := mul_le_mul ha' hb' (by positivity) (by positivity)
    nlinarith
  · nlinarith

theorem short_high_polynomial_bound (n m α β : ℝ)
    (hn : 8 ≤ |n|) (hm : 8 ≤ |m|)
    (hα : 0 ≤ α ∧ α ≤ 1/2) (hβ : 0 ≤ β ∧ β ≤ 1/4) :
    |45*n*m-(15/4:ℝ)*(n-m)^2+45*α*(n+m)+45*β| ≤
      (45*(17/16:ℝ)^2/64+(15/4:ℝ)*(1/4:ℝ)^2)*n^2*m^2 := by
  have hs : |n-m| ≤ |n|+|m| := abs_sub n m
  have hs2 : (n-m)^2 ≤ (|n|+|m|)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (n-m)) hs 2
  have h0 : |45*n*m-(15/4:ℝ)*(n-m)^2| ≤
      45*|n| *|m|+(15/4:ℝ)*(|n|+|m|)^2 := by
    calc
      _ ≤ |45*n*m|+|(15/4:ℝ)*(n-m)^2| := abs_sub _ _
      _ = 45*|n| *|m|+(15/4:ℝ)*(n-m)^2 := by
        norm_num [abs_mul,abs_of_nonneg (sq_nonneg (n-m))]
      _ ≤ _ := by gcongr
  have h1 : |45*α*(n+m)| ≤ (45/2:ℝ)*(|n|+|m|) := by
    calc
      _ = 45*α*|n+m| := by simp [abs_mul,abs_of_nonneg hα.1]
      _ ≤ 45*(1/2:ℝ)*(|n|+|m|) := by
        gcongr
        · exact hα.2
        · exact abs_add_le n m
      _ = _ := by ring
  have h2 : |45*β| ≤ (45/4:ℝ) := by
    rw [abs_mul, abs_of_nonneg hβ.1]
    norm_num
    linarith [hβ.2]
  have h3 := abs_add_le (45*n*m-(15/4:ℝ)*(n-m)^2) (45*α*(n+m))
  have h4 := abs_add_le (45*n*m-(15/4:ℝ)*(n-m)^2+45*α*(n+m)) (45*β)
  have hw := short_high_weight_bounds |n| |m| hn hm
  simp only [sq_abs] at hw
  nlinarith

theorem short_bernstein_first_weights (j : Fin 5) :
    (0:ℝ) ≤ (shortBernsteinWeight j 1:ℝ) ∧
    (shortBernsteinWeight j 1:ℝ) ≤ 1/2 ∧
    (0:ℝ) ≤ (shortBernsteinWeight j 2:ℝ) ∧
    (shortBernsteinWeight j 2:ℝ) ≤ 1/4 := by
  fin_cases j <;> norm_num [shortBernsteinWeight, Nat.choose]

theorem short_raw_off_diagonal (r : ℝ) (h : ℕ → ℝ)
    (j : Fin 5) (n m : ℤ) (hne : n ≠ m) :
    shortRawBernsteinEntry r h j n m = r *
      (45*(2*(n:ℝ))*(2*(m:ℝ))-(15/4:ℝ)*(2*(n:ℝ)-2*(m:ℝ))^2+
       45*(shortBernsteinWeight j 1:ℝ)*(2*(n:ℝ)+2*(m:ℝ))+
       45*(shortBernsteinWeight j 2:ℝ)) * h (n-m).natAbs := by
  have hne2 : (2:ℤ)*n ≠ 2*m := by omega
  have hidx : (2*n-2*m).natAbs/2 = (n-m).natAbs := by
    rw [← mul_sub, Int.natAbs_mul]
    norm_num
  have hrev : (2*m-2*n).natAbs/2 = (n-m).natAbs := by
    rw [← Int.natAbs_neg (2*n-2*m), neg_sub] at hidx
    exact hidx
  fin_cases j <;>
    norm_num [shortRawBernsteinEntry,shortBlochEntry,shortBernsteinWeight,
      Fin.sum_univ_succ,Nat.choose,hne,Ne.symm hne,hne2,Ne.symm hne2,hidx,hrev] <;> ring

/-- Every genuine off-diagonal high-frequency entry has the common
geometric majorant, before division by the positive Fourier weights. -/
theorem short_actual_raw_off_diagonal_bound (j : Fin 5) (n m : ℤ)
    (hne : n ≠ m) (hn : 4 ≤ n.natAbs) (hm : 4 ≤ m.natAbs) :
    |shortRawBernsteinEntry lemniscateFrequencySquared
      (fourierCoefficient lemniscateFrequencySquared nome) j n m| ≤
      (shortHighOffCoefficient:ℝ)*((n-m).natAbs:ℝ)*(qb:ℝ)^(n-m).natAbs*
        (2*(n:ℝ))^2*(2*(m:ℝ))^2 := by
  have hcast (v : ℤ) (hv : 4 ≤ v.natAbs) : 8 ≤ |2*(v:ℝ)| := by
    have hc : (4:ℝ) ≤ (v.natAbs:ℝ) := by exact_mod_cast hv
    rw [Nat.cast_natAbs,Int.cast_abs] at hc
    rw [abs_mul]
    norm_num
    linarith
  have hw := short_bernstein_first_weights j
  have hp := short_high_polynomial_bound (2*(n:ℝ)) (2*(m:ℝ))
    (shortBernsteinWeight j 1:ℝ) (shortBernsteinWeight j 2:ℝ)
    (hcast n hn) (hcast m hm) ⟨hw.1,hw.2.1⟩ ⟨hw.2.2.1,hw.2.2.2⟩
  have hd : 0 < (n-m).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr hne)
  have hh := common_index_coefficient_majorant (n-m).natAbs (n-m).natAbs hd le_rfl
  have hr : |lemniscateFrequencySquared| ≤ (rhi:ℝ) := by
    have h := short_frequency_enclosure
    norm_num [Contains,shortFrequencyInterval] at h
    rw [abs_le]
    norm_num [rhi]
    constructor <;> linarith
  have ht := mul_le_mul
    (mul_le_mul hr hp (abs_nonneg _) (by norm_num [rhi])) hh (abs_nonneg _)
    (by have hr0 : (0:ℝ) ≤ (rhi:ℝ) := by norm_num [rhi]
        positivity : (0:ℝ) ≤ (rhi:ℝ)*
      ((45*(17/16:ℝ)^2/64+(15/4:ℝ)*(1/4:ℝ)^2)*(2*(n:ℝ))^2*(2*(m:ℝ))^2))
  rw [short_raw_off_diagonal _ _ j n m hne, abs_mul, abs_mul]
  apply ht.trans_eq
  simp only [shortHighOffCoefficient,Rat.cast_mul,Rat.cast_div,Rat.cast_add,
    Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one]
  ring

end Lemniscate
