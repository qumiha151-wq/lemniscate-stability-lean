import Lemniscate.OddPolynomialSemantics
import Lemniscate.CoefficientMajorant

/-! The endpoint-sign rule in the paper really majorizes the absolute value
of every odd-frequency off-diagonal polynomial throughout [0,1/2]. This connects
the exact rational list used in certificates with the real coefficient entry. -/
namespace Lemniscate.OddArithmetic
open Finset CoarseArithmetic

noncomputable def oddEntryPolynomial (n m : ℤ) (α : ℝ) : ℝ :=
  45*((n:ℝ)+α)*((m:ℝ)+α)-(15/4)*((n:ℝ)-(m:ℝ))^2

def oddEntryCoefficients (n m : ℤ) : Poly :=
  [45*(n:ℚ)*(m:ℚ)-(15/4)*((n:ℚ)-(m:ℚ))^2,45*((n:ℚ)+(m:ℚ)),45]

def oddEntryMajorantList (n m : ℤ) : Poly :=
  let p := oddEntryCoefficients n m
  if 0 ≤ min (polyEval p 0) (polyEval p (1/2)) then p
  else if max (polyEval p 0) (polyEval p (1/2)) ≤ 0 then polyScale p (-1)
  else p.map abs

theorem realEval_polyEval_rat (p : Poly) (t : ℚ) :
    (polyEval p t : ℝ) = realEval p (t:ℝ) := by
  rw [realEval_eq_sum, polyEval, sumTo_eq_sum_range]
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_pow]

theorem realEval_odd_entry (n m : ℤ) (α : ℝ) :
    realEval (oddEntryCoefficients n m) α = oddEntryPolynomial n m α := by
  rw [oddEntryCoefficients, realEval_quadratic]
  unfold oddEntryPolynomial
  push_cast
  ring

theorem odd_entry_difference (n m : ℤ) (α β : ℝ) :
    oddEntryPolynomial n m β-oddEntryPolynomial n m α =
      45*(β-α)*((n:ℝ)+(m:ℝ)+α+β) := by
  unfold oddEntryPolynomial
  ring

theorem odd_pair_sum_dichotomy (n m : ℤ) (hn : Odd n) (hm : Odd m) :
    0 ≤ (n:ℝ)+(m:ℝ) ∨ (n:ℝ)+(m:ℝ) ≤ -2 := by
  rcases hn with ⟨j, hj⟩
  rcases hm with ⟨k, hk⟩
  have hi : (0:ℤ) ≤ n+m ∨ n+m ≤ -2 := by omega
  rcases hi with hi | hi
  · left
    exact_mod_cast hi
  · right
    exact_mod_cast hi

theorem odd_entry_endpoint_bounds (n m : ℤ) (hn : Odd n) (hm : Odd m)
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    min (oddEntryPolynomial n m 0) (oddEntryPolynomial n m (1/2)) ≤
      oddEntryPolynomial n m α ∧
    oddEntryPolynomial n m α ≤
      max (oddEntryPolynomial n m 0) (oddEntryPolynomial n m (1/2)) := by
  rcases odd_pair_sum_dichotomy n m hn hm with hs | hs
  · have h0 : oddEntryPolynomial n m 0 ≤ oddEntryPolynomial n m α := by
      have hd := odd_entry_difference n m 0 α
      have hz : 0 ≤ 45*(α-0)*((n:ℝ)+(m:ℝ)+0+α) := by positivity
      linarith
    have h1 : oddEntryPolynomial n m α ≤ oddEntryPolynomial n m (1/2) := by
      have hd := odd_entry_difference n m α (1/2)
      have hz : 0 ≤ 45*(1/2-α)*((n:ℝ)+(m:ℝ)+α+1/2) := by
        exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
      linarith
    exact ⟨(min_le_left _ _).trans h0, h1.trans (le_max_right _ _)⟩
  · have h0 : oddEntryPolynomial n m α ≤ oddEntryPolynomial n m 0 := by
      have hd := odd_entry_difference n m 0 α
      have hz : 45*(α-0)*((n:ℝ)+(m:ℝ)+0+α) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      linarith
    have h1 : oddEntryPolynomial n m (1/2) ≤ oddEntryPolynomial n m α := by
      have hd := odd_entry_difference n m α (1/2)
      have hz : 45*(1/2-α)*((n:ℝ)+(m:ℝ)+α+1/2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg (by norm_num) (by linarith)) (by linarith)
      linarith
    exact ⟨(min_le_right _ _).trans h1, h0.trans (le_max_left _ _)⟩

theorem realEval_abs_majorant (p : Poly) (α : ℝ) (hα : 0 ≤ α) :
    |realEval p α| ≤ realEval (p.map abs) α := by
  have hc (j : ℕ) : coeff (p.map abs) j = |coeff p j| := by
    simp only [coeff, List.getElem?_map]
    simpa only [abs_zero] using Option.getD_map (fun x : ℚ => |x|) 0 p[j]?
  rw [realEval_eq_sum, realEval_eq_sum]
  simp only [List.length_map, hc, Rat.cast_abs]
  calc
    _ ≤ ∑ j ∈ range p.length, |(coeff p j : ℝ)*α^j| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_mul, abs_of_nonneg (pow_nonneg hα j)]

theorem odd_entry_majorant_sound (n m : ℤ) (hn : Odd n) (hm : Odd m)
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    |oddEntryPolynomial n m α| ≤ realEval (oddEntryMajorantList n m) α := by
  have hb := odd_entry_endpoint_bounds n m hn hm α hα hα'
  unfold oddEntryMajorantList
  dsimp only
  split_ifs with hp hn'
  · have h0 : 0 ≤ oddEntryPolynomial n m 0 := by
      have h := (le_min_iff.mp hp).1
      have hc : (0:ℝ) ≤ (polyEval (oddEntryCoefficients n m) 0 : ℝ) := by exact_mod_cast h
      simpa only [realEval_polyEval_rat, realEval_odd_entry, Rat.cast_zero] using hc
    have h1 : 0 ≤ oddEntryPolynomial n m (1/2) := by
      have h := (le_min_iff.mp hp).2
      have hc : (0:ℝ) ≤ (polyEval (oddEntryCoefficients n m) (1/2) : ℝ) := by exact_mod_cast h
      norm_num only [realEval_polyEval_rat, realEval_odd_entry, Rat.cast_div,
        Rat.cast_one, Rat.cast_ofNat] at hc
      exact hc
    rw [realEval_odd_entry, abs_of_nonneg ((le_min h0 h1).trans hb.1)]
  · have h0 : oddEntryPolynomial n m 0 ≤ 0 := by
      have h := (max_le_iff.mp hn').1
      have hc : (polyEval (oddEntryCoefficients n m) 0 : ℝ) ≤ 0 := by exact_mod_cast h
      simpa only [realEval_polyEval_rat, realEval_odd_entry, Rat.cast_zero] using hc
    have h1 : oddEntryPolynomial n m (1/2) ≤ 0 := by
      have h := (max_le_iff.mp hn').2
      have hc : (polyEval (oddEntryCoefficients n m) (1/2) : ℝ) ≤ 0 := by exact_mod_cast h
      norm_num only [realEval_polyEval_rat, realEval_odd_entry, Rat.cast_div,
        Rat.cast_one, Rat.cast_ofNat] at hc
      exact hc
    rw [realEval_scale, realEval_odd_entry, abs_of_nonpos (hb.2.trans (max_le h0 h1))]
    norm_num
  · rw [← realEval_odd_entry]
    exact realEval_abs_majorant _ α hα

theorem absoluteEntryPolynomial_eq (n m : ℤ) :
    absoluteEntryPolynomial n m = polyScale (oddEntryMajorantList n m)
      (rhi*hUpper ((n-m).natAbs/2)) := rfl

theorem odd_half_distance_pos (n m : ℤ) (hn : Odd n) (hm : Odd m) (hne : n ≠ m) :
    0 < (n-m).natAbs/2 := by
  rcases hn with ⟨j, hj⟩
  rcases hm with ⟨k, hk⟩
  have hna := Int.natCast_natAbs (n-m)
  have ha := le_abs_self (n-m)
  have hb := neg_le_abs (n-m)
  omega

theorem theta_nome_odd_off_diagonal_bound (n m : ℤ) (hn : Odd n) (hm : Odd m)
    (hne : n ≠ m) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    |thetaParameter*fourierCoefficient thetaParameter nome ((n-m).natAbs/2)*
      oddEntryPolynomial n m α| ≤ realEval (absoluteEntryPolynomial n m) α := by
  let j := (n-m).natAbs/2
  have hj : 0 < j := odd_half_distance_pos n m hn hm hne
  have hcoef := theta_nome_coefficient_majorant j hj
  have hu := (theta_nome_fourier_enclosure j).2
  have hr : 0 ≤ thetaParameter := (by norm_num [rlo] : (0:ℝ) ≤ (rlo:ℝ)).trans
    (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, thetaRLower]) (by norm_num [rhi, thetaRUpper])).1
  have hupper : 0 ≤ (hUpper j : ℝ) := hcoef.1.trans hu
  have hscalar : thetaParameter*fourierCoefficient thetaParameter nome j ≤
      (rhi:ℝ)*(hUpper j:ℝ) :=
    mul_le_mul (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, thetaRLower]) (by norm_num [rhi, thetaRUpper])).2 hu hcoef.1 (by norm_num [rhi])
  have hv := odd_entry_majorant_sound n m hn hm α hα hα'
  rw [absoluteEntryPolynomial_eq, realEval_scale, Rat.cast_mul]
  rw [abs_mul, abs_mul, abs_of_nonneg hr, abs_of_nonneg hcoef.1]
  exact mul_le_mul hscalar hv (abs_nonneg _) (mul_nonneg (by norm_num [rhi]) hupper)

end Lemniscate.OddArithmetic
