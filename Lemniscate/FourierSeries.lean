import Lemniscate.FourierEnclosure
import Lemniscate.GeometricTails
import Lemniscate.OddPositivity
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Convergence and the constant-term enclosure for the coefficient formula.
The Jacobi Fourier identity and transcendental parameter bounds are still
separate obligations; they are not assumed as new axioms. -/
namespace Lemniscate.CoarseArithmetic
open Finset

theorem evenCoefficient_nonneg (r q : ℝ) (j : ℕ)
    (hr : 0 ≤ r) (hq : 0 ≤ q) (hq1 : q < 1) :
    0 ≤ evenCoefficient r q j := by
  by_cases hj : j = 0
  · simp [evenCoefficient, hj]
  have hd : 0 < 1-q^(2*j) := sub_pos.mpr
    (pow_lt_one₀ hq hq1 (Nat.mul_ne_zero (by decide) hj))
  unfold evenCoefficient
  positivity

theorem evenCoefficient_majorant (r q : ℝ) (j : ℕ)
    (hr : 0 ≤ r) (hq : 0 ≤ q) (hq1 : q < 1) :
    evenCoefficient r q j ≤ (8*r/(1-q^2))*((j:ℝ)*q^j) := by
  by_cases hj : j = 0
  · simp [evenCoefficient, hj]
  have hp : q^(2*j) ≤ q^2 :=
    pow_le_pow_of_le_one hq hq1.le (by omega)
  have hd : 0 < 1-q^2 := sub_pos.mpr (pow_lt_one₀ hq hq1 (by decide))
  calc
    evenCoefficient r q j ≤ 8*r*(j:ℝ)*q^j/(1-q^2) := by
      exact div_le_div₀ (by positivity) le_rfl hd (sub_le_sub_left hp 1)
    _ = _ := by ring

theorem coarse_fourier_tail_majorant (r q : ℝ) (L : ℕ)
    (hr : Contains ⟨rlo,rhi⟩ r) (hq : Contains ⟨qlo,qhi⟩ q)
    (hL : 0 < L) (n : ℕ) :
    evenCoefficient r q (n+L) ≤
      (8*(rhi:ℝ)/(1-(qhi:ℝ)^2))*(((n+L:ℕ):ℝ)*(qhi:ℝ)^(n+L)) := by
  have hj : 0 < n+L := by omega
  have hu := (positive_fourier_enclosure r q (n+L) hr hq hj).2
  change evenCoefficient r q (n+L) ≤ (hUpper (n+L) : ℝ) at hu
  rw [hUpper, if_neg (Nat.ne_of_gt hj)] at hu
  have hm := evenCoefficient_majorant (rhi:ℝ) (qhi:ℝ) (n+L)
    (by norm_num [rhi]) (by norm_num [qhi]) (by norm_num [qhi])
  apply le_trans _ hm
  simpa [hUpperPositive, evenCoefficient] using hu

theorem summable_fourier_tail (r q : ℝ) (L : ℕ)
    (hr : Contains ⟨rlo,rhi⟩ r) (hq : Contains ⟨qlo,qhi⟩ q) (hL : 0 < L) :
    Summable (fun n : ℕ => evenCoefficient r q (n+L)) := by
  have hs := (tail1_sound qhi (by norm_num [qhi, Real.norm_eq_abs]) L).summable
  apply Summable.of_nonneg_of_le _ (coarse_fourier_tail_majorant r q L hr hq hL)
    (hs.mul_left (8*(rhi:ℝ)/(1-(qhi:ℝ)^2)))
  intro n
  exact evenCoefficient_nonneg r q (n+L)
    ((by norm_num [rlo] : (0:ℝ) ≤ (rlo:ℝ)).trans hr.1)
    ((by norm_num [qlo] : (0:ℝ) ≤ (qlo:ℝ)).trans hq.1)
    (hq.2.trans_lt (by norm_num [qhi]))

theorem fourier_tail_bound (r q : ℝ) (L : ℕ)
    (hr : Contains ⟨rlo,rhi⟩ r) (hq : Contains ⟨qlo,qhi⟩ q) (hL : 0 < L) :
    (∑' n : ℕ, evenCoefficient r q (n+L)) ≤
      (8*(rhi:ℝ)/(1-(qhi:ℝ)^2))*(tail1 qhi L : ℝ) := by
  have hs := (tail1_sound qhi (by norm_num [qhi, Real.norm_eq_abs]) L).mul_left
    (8*(rhi:ℝ)/(1-(qhi:ℝ)^2))
  rw [← hs.tsum_eq]
  exact (summable_fourier_tail r q L hr hq hL).tsum_le_tsum
    (coarse_fourier_tail_majorant r q L hr hq hL) hs.summable

noncomputable def constantCoefficient (r q : ℝ) : ℝ :=
  1-2*(∑' n : ℕ, evenCoefficient r q (n+1))

theorem constant_fourier_enclosure (r q : ℝ)
    (hr : Contains ⟨rlo,rhi⟩ r) (hq : Contains ⟨qlo,qhi⟩ q) :
    Contains (hInterval 0) (constantCoefficient r q) := by
  have hs := summable_fourier_tail r q 1 hr hq (by decide)
  have hsplit := hs.sum_add_tsum_nat_add 4
  have hlo : (sumTo 4 (fun k => hLowerPositive (k+1)) : ℝ) ≤
      ∑ k ∈ range 4, evenCoefficient r q (k+1) := by
    rw [OddArithmetic.sumTo_eq_sum_range, Rat.cast_sum]
    apply sum_le_sum
    intro k hk
    have h := (positive_fourier_enclosure r q (k+1) hr hq (by omega)).1
    simpa [hInterval, hLower] using h
  have hhi : (∑ k ∈ range 4, evenCoefficient r q (k+1)) ≤
      (sumTo 4 (fun k => hUpperPositive (k+1)) : ℝ) := by
    rw [OddArithmetic.sumTo_eq_sum_range, Rat.cast_sum]
    apply sum_le_sum
    intro k hk
    have h := (positive_fourier_enclosure r q (k+1) hr hq (by omega)).2
    simpa [hInterval, hUpper] using h
  have ht := fourier_tail_bound r q 5 hr hq (by decide)
  have ht2 : 2*(∑' n : ℕ, evenCoefficient r q (n+5)) ≤
      16*(rhi:ℝ)*(tail1 qhi 5 : ℝ)/(1-(qhi:ℝ)^2) := by
    calc
      _ ≤ 2*((8*(rhi:ℝ)/(1-(qhi:ℝ)^2))*(tail1 qhi 5 : ℝ)) :=
        mul_le_mul_of_nonneg_left ht (by norm_num)
      _ = _ := by ring
  have ht0 : 0 ≤ ∑' n : ℕ, evenCoefficient r q (n+5) := by
    apply tsum_nonneg
    intro n
    exact evenCoefficient_nonneg r q (n+5)
      ((by norm_num [rlo] : (0:ℝ) ≤ (rlo:ℝ)).trans hr.1)
      ((by norm_num [qlo] : (0:ℝ) ≤ (qlo:ℝ)).trans hq.1)
      (hq.2.trans_lt (by norm_num [qhi]))
  norm_num only [Nat.add_assoc] at hsplit
  change (hLower 0 : ℝ) ≤ constantCoefficient r q ∧
    constantCoefficient r q ≤ (hUpper 0 : ℝ)
  simp only [hLower, hUpper, ite_true, Rat.cast_sub, Rat.cast_one,
    Rat.cast_mul, Rat.cast_ofNat, Rat.cast_div, Rat.cast_pow, constantCoefficient]
  constructor <;> linarith

end Lemniscate.CoarseArithmetic
