import Lemniscate.OddMatrix

/-! The common off-diagonal majorant used for infinite odd-row tails. The
distance is the actual integer half-distance of two odd Fourier frequencies. -/
namespace Lemniscate.OddArithmetic
open CoarseArithmetic

theorem odd_half_distance_abs (n m : ℤ) (hn : Odd n) (hm : Odd m) :
    |(n:ℝ)-(m:ℝ)| = 2*(((n-m).natAbs/2:ℕ):ℝ) := by
  rcases hn with ⟨j, hj⟩
  rcases hm with ⟨k, hk⟩
  have he : n-m = 2*(j-k) := by omega
  have hd : (n-m).natAbs = 2*(j-k).natAbs := by
    rw [he, Int.natAbs_mul]
    rfl
  have hcast : |(n:ℝ)-(m:ℝ)| = ((n-m).natAbs:ℝ) := by
    have ht := congrArg (fun z : ℤ => (z:ℝ)) (Int.natCast_natAbs (n-m))
    simpa only [Int.cast_natCast, Int.cast_abs, Int.cast_sub] using ht.symm
  rw [hcast, hd, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), Nat.cast_mul]
  norm_num

theorem odd_real_polynomial_majorant (x y v l : ℝ) (hv : |x| ≤ v)
    (hl : 0 ≤ l) (hd : |x-y| = 2*l) :
    |45*x*y-(15/4)*(x-y)^2| ≤ 45*(v^2+2*v*l+l^2/3) := by
  have hv0 : 0 ≤ v := (abs_nonneg x).trans hv
  have hx2 : x^2 ≤ v^2 := by
    calc
      _ = |x|^2 := (sq_abs x).symm
      _ ≤ v^2 := pow_le_pow_left₀ (abs_nonneg x) hv 2
  have hd2 : (x-y)^2 = 4*l^2 := by nlinarith [sq_abs (x-y)]
  have hm : |x| * |x-y| ≤ v*(2*l) := by
    rw [hd]
    exact mul_le_mul_of_nonneg_right hv (by positivity)
  calc
    _ = |45*(x^2-x*(x-y)-(x-y)^2/12)| := by
      congr 1
      ring
    _ = 45*|x^2-x*(x-y)-(x-y)^2/12| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 45)]
    _ ≤ 45*(x^2+|x| * |x-y|+(x-y)^2/12) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc
        _ ≤ |x^2-x*(x-y)|+|(x-y)^2/12| := by
          simpa only [sub_zero, zero_sub, abs_neg] using
            (abs_sub_le (x^2-x*(x-y)) 0 ((x-y)^2/12))
        _ ≤ (|x^2|+|x*(x-y)|)+|(x-y)^2/12| := by
          have hb : |x^2-x*(x-y)| ≤ |x^2|+|x*(x-y)| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              (abs_sub_le (x^2) 0 (x*(x-y)))
          linarith
        _ = _ := by rw [abs_of_nonneg (sq_nonneg x), abs_mul,
          abs_of_nonneg (by positivity : 0 ≤ (x-y)^2/12)]
    _ ≤ _ := by nlinarith

theorem odd_entry_polynomial_tail_bound (n m : ℤ) (hn : Odd n) (hm : Odd m)
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    |oddEntryPolynomial n m α| ≤
      45*((|(n:ℝ)|+1/2)^2+2*(|(n:ℝ)|+1/2)*(((n-m).natAbs/2:ℕ):ℝ)+
        (((n-m).natAbs/2:ℕ):ℝ)^2/3) := by
  have hv : |(n:ℝ)+α| ≤ |(n:ℝ)|+1/2 := by
    calc
      _ ≤ |(n:ℝ)|+|α| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_nonneg hα]; linarith
  have hd : |((n:ℝ)+α)-((m:ℝ)+α)| = 2*(((n-m).natAbs/2:ℕ):ℝ) := by
    rw [show (n:ℝ)+α-((m:ℝ)+α) = (n:ℝ)-(m:ℝ) by ring]
    exact odd_half_distance_abs n m hn hm
  have hb := odd_real_polynomial_majorant ((n:ℝ)+α) ((m:ℝ)+α) (|(n:ℝ)|+1/2)
    (((n-m).natAbs/2:ℕ):ℝ) hv (Nat.cast_nonneg _) hd
  simpa only [oddEntryPolynomial, add_sub_add_right_eq_sub] using hb

theorem odd_matrix_off_tail_bound (n m : ℤ) (hn : Odd n) (hm : Odd m) (hne : n ≠ m)
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    |oddMatrixEntry α n m| ≤
      (45*(rhi:ℝ)*(H:ℝ))*(((n-m).natAbs/2:ℕ):ℝ)*(qb:ℝ)^((n-m).natAbs/2)*
        ((|(n:ℝ)|+1/2)^2+2*(|(n:ℝ)|+1/2)*(((n-m).natAbs/2:ℕ):ℝ)+
          (((n-m).natAbs/2:ℕ):ℝ)^2/3) := by
  let j := (n-m).natAbs/2
  let v : ℝ := |(n:ℝ)|+1/2
  have hj : 0 < j := odd_half_distance_pos n m hn hm hne
  have hc := theta_nome_coefficient_majorant j hj
  have hr : 0 ≤ thetaParameter :=
    (by norm_num [rlo] : (0:ℝ) ≤ (rlo:ℝ)).trans actual_nome_theta_r_bounds.1
  have hs : thetaParameter*fourierCoefficient thetaParameter nome j ≤
      (rhi:ℝ)*((H:ℝ)*((j:ℝ)*(qb:ℝ)^j)) :=
    mul_le_mul actual_nome_theta_r_bounds.2 hc.2 hc.1 (by norm_num [rhi])
  have hb := odd_entry_polynomial_tail_bound n m hn hm α hα hα'
  rw [oddMatrixEntry, if_neg hne, abs_mul, abs_mul, abs_of_nonneg hr, abs_of_nonneg hc.1]
  calc
    _ ≤ ((rhi:ℝ)*((H:ℝ)*((j:ℝ)*(qb:ℝ)^j)))*(45*(v^2+2*v*(j:ℝ)+(j:ℝ)^2/3)) :=
      mul_le_mul hs hb (abs_nonneg _) (by
        have hh : 0 ≤ (H:ℝ) := by norm_num [H, rhi, qb]
        have hq : 0 ≤ (qb:ℝ) := by norm_num [qb]
        have hrhi : 0 ≤ (rhi:ℝ) := by norm_num [rhi]
        positivity)
    _ = _ := by dsimp only [j, v]; ring

end Lemniscate.OddArithmetic
