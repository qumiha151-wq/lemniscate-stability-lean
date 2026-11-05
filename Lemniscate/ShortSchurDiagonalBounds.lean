import Lemniscate.ShortSchurRawBounds

/-! The negative quartic Bernstein coefficient factors exactly.
This gives the entire far-diagonal estimate by monotonicity. -/
namespace Lemniscate
open CoarseArithmetic

theorem short_bernstein_quartic_lower (j : Fin 5) (n : ℝ) (hn : 30 ≤ |n|) :
    (|n|-1/2)^4 ≤ n^(4-j.val)*(n+1/2)^j.val := by
  have hd : 0 ≤ |n|-1/2 := by linarith
  have hdn : |n|-1/2 ≤ |n| := by linarith
  have hdp : |n|-1/2 ≤ |n+1/2| := by
    have h := abs_sub (n+1/2) (1/2:ℝ)
    norm_num at h
    linarith
  have ht := mul_le_mul (pow_le_pow_left₀ hd hdn (4-j.val))
    (pow_le_pow_left₀ hd hdp j.val) (pow_nonneg hd _)
    (pow_nonneg (abs_nonneg n) _)
  have he : 4-j.val+j.val=4 := by omega
  rw [← pow_add, he] at ht
  apply ht.trans_eq
  by_cases hn0 : 0 ≤ n
  · rw [abs_of_nonneg hn0, abs_of_nonneg (by linarith : 0 ≤ n+1/2)]
  · have hnneg : n < 0 := lt_of_not_ge hn0
    have hnp : n+1/2 ≤ 0 := by rw [abs_of_neg hnneg] at hn; linarith
    rw [abs_of_neg hnneg,abs_of_nonpos hnp]
    fin_cases j <;> norm_num <;> ring_nf <;> simp

theorem short_bernstein_quadratic_bounds (j : Fin 5) (n : ℝ) (hn : 30 ≤ |n|) :
    0 ≤ n^2+2*(shortBernsteinWeight j 1:ℝ)*n+(shortBernsteinWeight j 2:ℝ) ∧
    n^2+2*(shortBernsteinWeight j 1:ℝ)*n+(shortBernsteinWeight j 2:ℝ) ≤ (|n|+1/2)^2 := by
  have hw := short_bernstein_first_weights j
  have ht : |2*(shortBernsteinWeight j 1:ℝ)*n| ≤ |n| := by
    rw [abs_mul,abs_of_nonneg (mul_nonneg (by norm_num) hw.1)]
    have h := mul_le_mul_of_nonneg_right hw.2.1 (abs_nonneg n)
    nlinarith
  have hs := sq_abs n
  constructor <;> nlinarith [le_abs_self (2*(shortBernsteinWeight j 1:ℝ)*n),
    neg_abs_le (2*(shortBernsteinWeight j 1:ℝ)*n)]

theorem short_raw_diagonal (r : ℝ) (h : ℕ → ℝ) (j : Fin 5) (n : ℤ) :
    shortRawBernsteinEntry r h j n n =
      45*r*h 0*((2*(n:ℝ))^2+2*(shortBernsteinWeight j 1:ℝ)*(2*(n:ℝ))+
        (shortBernsteinWeight j 2:ℝ))-
      4*r^2*(2*(n:ℝ))^(4-j.val)*(2*(n:ℝ)+1/2)^j.val-83/2 := by
  fin_cases j <;>
    norm_num [shortRawBernsteinEntry,shortBlochEntry,shortBernsteinWeight,
      Fin.sum_univ_succ,Nat.choose] <;> ring

theorem short_far_diagonal_bound (r c n : ℝ) (j : Fin 5)
    (hr : (rlo:ℝ) ≤ r ∧ r ≤ (rhi:ℝ)) (hc : c ≤ 1) (hn : 30 ≤ |n|) :
    45*r*c*(n^2+2*(shortBernsteinWeight j 1:ℝ)*n+(shortBernsteinWeight j 2:ℝ))-
        4*r^2*n^(4-j.val)*(n+1/2)^j.val-83/2 ≤
      (-4*(rlo:ℝ)^2*(1-1/60:ℝ)^4+45*(rhi:ℝ)*(1+1/60:ℝ)^2/900)*n^4 := by
  let Q := n^2+2*(shortBernsteinWeight j 1:ℝ)*n+(shortBernsteinWeight j 2:ℝ)
  let P := n^(4-j.val)*(n+1/2)^j.val
  have hQ := short_bernstein_quadratic_bounds j n hn
  have hP := short_bernstein_quartic_lower j n hn
  have hrlo : (0:ℝ) ≤ (rlo:ℝ) := by norm_num [rlo]
  have hr0 : 0 ≤ r := hrlo.trans hr.1
  have hrhi : (0:ℝ) ≤ (rhi:ℝ) := by norm_num [rhi]
  have hp0 : 0 ≤ P := (pow_nonneg (by linarith : 0 ≤ |n|-1/2) 4).trans hP
  have hp : (1-1/60:ℝ)^4*n^4 ≤ P := by
    have hbase : (1-1/60:ℝ)*|n| ≤ |n|-1/2 := by linarith
    have h := pow_le_pow_left₀ (by positivity) hbase 4
    have hs : |n|^4=n^4 := by
      calc
        _ = (|n|^2)^2 := by ring
        _ = (n^2)^2 := by rw [sq_abs]
        _ = _ := by ring
    rw [mul_pow,hs] at h
    exact h.trans hP
  have hq : Q ≤ (1+1/60:ℝ)^2/900*n^4 := by
    have hbase : |n|+1/2 ≤ (1+1/60:ℝ)*|n| := by linarith
    have h := pow_le_pow_left₀ (by positivity) hbase 2
    rw [mul_pow,sq_abs] at h
    have hn2 : 900 ≤ n^2 := by nlinarith [sq_abs n]
    have hn4 : 900*n^2 ≤ n^4 := by nlinarith [mul_nonneg (sq_nonneg n) (sub_nonneg.mpr hn2)]
    dsimp only [Q]
    nlinarith
  have hrc : r*c*Q ≤ r*Q := by nlinarith [mul_le_mul_of_nonneg_left hc (mul_nonneg hr0 hQ.1)]
  have hrq := mul_le_mul hr.2 hq hQ.1 hrhi
  have hr2 := pow_le_pow_left₀ hrlo hr.1 2
  have hrp := mul_le_mul hr2 hp (by positivity : (0:ℝ)≤(1-1/60:ℝ)^4*n^4) (sq_nonneg r)
  dsimp only [Q,P] at hrc hrq hrp
  nlinarith only [hrc,hrq,hrp]

theorem short_actual_constant_le_one :
    fourierCoefficient lemniscateFrequencySquared nome 0 ≤ 1 := by
  have hs : 0 ≤ ∑' k : ℕ, evenCoefficient lemniscateFrequencySquared nome (k+1) := by
    apply tsum_nonneg
    intro k
    simpa only [fourierCoefficient,if_neg (by omega : k+1≠0)] using
      (frequency_nome_coefficient_majorant (k+1) (by omega)).1
  simp [fourierCoefficient,constantCoefficient]
  linarith

theorem short_actual_raw_diagonal_bound (j : Fin 5) (n : ℤ) (hn : 15 ≤ n.natAbs) :
    shortRawBernsteinEntry lemniscateFrequencySquared
      (fourierCoefficient lemniscateFrequencySquared nome) j n n ≤
      (-4*(rlo:ℝ)^2*(1-1/60:ℝ)^4+45*(rhi:ℝ)*(1+1/60:ℝ)^2/900)*(2*(n:ℝ))^4 := by
  have hr : (rlo:ℝ) ≤ lemniscateFrequencySquared ∧
      lemniscateFrequencySquared ≤ (rhi:ℝ) := by
    have h := short_frequency_enclosure
    norm_num [Contains,shortFrequencyInterval] at h
    norm_num [rlo,rhi]
    constructor <;> linarith
  have hn' : 30 ≤ |2*(n:ℝ)| := by
    have h : (15:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast hn
    rw [Nat.cast_natAbs,Int.cast_abs] at h
    rw [abs_mul]
    norm_num
    linarith
  rw [short_raw_diagonal]
  exact short_far_diagonal_bound _ _ _ j hr short_actual_constant_le_one hn'

end Lemniscate
