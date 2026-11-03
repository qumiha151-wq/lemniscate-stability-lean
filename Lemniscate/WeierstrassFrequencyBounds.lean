import Lemniscate.NomeBounds
import Lemniscate.GeometricTails

/-! Bounds for the squared fundamental frequency derived from the actual
square-lattice series. No theta-function identity is assumed. -/
namespace Lemniscate

noncomputable def weierstrassHalfPeriodTerm (q : ℝ) (n : ℕ) : ℝ :=
  q^(2*(n+1))/(1+q^(2*(n+1)))^2 + q^(2*(n+1))/(1-q^(2*(n+1)))^2

end Lemniscate

namespace Lemniscate.CoarseArithmetic
open Finset

def frequencyLower : ℚ := 717770011046129997816/10^21
def frequencyUpper : ℚ := 717770011046129997825/10^21

noncomputable section

def lemniscateFrequencySquared : ℝ :=
  3/(4*(1+12*(∑' n : ℕ, weierstrassHalfPeriodTerm (Real.exp (-Real.pi)) n)))

private def lowerTerm (l u : ℝ) (n : ℕ) : ℝ :=
  l^(2*(n+1))/(1+u^(2*(n+1)))^2+l^(2*(n+1))/(1-l^(2*(n+1)))^2

private def upperTerm (l u : ℝ) (n : ℕ) : ℝ :=
  u^(2*(n+1))/(1+l^(2*(n+1)))^2+u^(2*(n+1))/(1-u^(2*(n+1)))^2

private theorem term_nonneg (q : ℝ) (hq : 0 ≤ q) (n : ℕ) :
    0 ≤ weierstrassHalfPeriodTerm q n := by
  dsimp only [weierstrassHalfPeriodTerm]
  positivity

private theorem term_interval (l q u : ℝ) (hl : 0 ≤ l) (hlq : l ≤ q)
    (hqu : q ≤ u) (hu : u < 1) (n : ℕ) :
    lowerTerm l u n ≤ weierstrassHalfPeriodTerm q n ∧
      weierstrassHalfPeriodTerm q n ≤ upperTerm l u n := by
  let k := 2*(n+1)
  have hq : 0 ≤ q := hl.trans hlq
  have hu0 : 0 ≤ u := hq.trans hqu
  have hqp : 0 ≤ q^k := pow_nonneg hq k
  have hup0 : 0 ≤ u^k := pow_nonneg hu0 k
  have hlow : l^k ≤ q^k := pow_le_pow_left₀ hl hlq k
  have hhigh : q^k ≤ u^k := pow_le_pow_left₀ hq hqu k
  have hup : u^k < 1 := pow_lt_one₀ hu0 hu (by dsimp only [k]; omega)
  have hq1 : q^k < 1 := hhigh.trans_lt hup
  constructor
  · dsimp only [lowerTerm,weierstrassHalfPeriodTerm]
    apply add_le_add
    · exact div_le_div₀ hqp hlow (by positivity)
        (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl (1:ℝ)) hhigh) 2)
    · exact div_le_div₀ hqp hlow (by positivity)
        (pow_le_pow_left₀ (sub_nonneg.mpr hq1.le) (sub_le_sub_left hlow 1) 2)
  · dsimp only [upperTerm,weierstrassHalfPeriodTerm]
    apply add_le_add
    · exact div_le_div₀ hup0 hhigh (by positivity)
        (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl (1:ℝ)) hlow) 2)
    · exact div_le_div₀ hup0 hhigh (by positivity)
        (pow_le_pow_left₀ (sub_nonneg.mpr hup.le) (sub_le_sub_left hhigh 1) 2)

private theorem term_majorant (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    weierstrassHalfPeriodTerm q n ≤ 2*q^(2*(n+1))/(1-q^2)^2 := by
  have hq2 : q^2 < 1 := pow_lt_one₀ hq hq1 (by decide)
  have hs : 0 ≤ q^(2*(n+1)) := pow_nonneg hq _
  have hp : q^(2*(n+1)) ≤ q^2 := pow_le_pow_of_le_one hq hq1.le (by omega)
  have hd : 0 < (1-q^2)^2 := sq_pos_of_pos (sub_pos.mpr hq2)
  have hplus : (1-q^2)^2 ≤ (1+q^(2*(n+1)))^2 :=
    pow_le_pow_left₀ (sub_nonneg.mpr hq2.le) (by nlinarith [sq_nonneg q]) 2
  have hminus : (1-q^2)^2 ≤ (1-q^(2*(n+1)))^2 :=
    pow_le_pow_left₀ (sub_nonneg.mpr hq2.le) (sub_le_sub_left hp 1) 2
  have h1 := div_le_div₀ hs (le_refl (q^(2*(n+1)))) hd hplus
  have h2 := div_le_div₀ hs (le_refl (q^(2*(n+1)))) hd hminus
  dsimp only [weierstrassHalfPeriodTerm]
  calc
    _ ≤ q^(2*(n+1))/(1-q^2)^2+q^(2*(n+1))/(1-q^2)^2 := add_le_add h1 h2
    _ = _ := by ring

private theorem series_tail (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (N : ℕ)
    : Summable (fun n : ℕ => weierstrassHalfPeriodTerm q (n+N)) ∧
      (∑' n : ℕ, weierstrassHalfPeriodTerm q (n+N)) ≤
        2*q^(2*(N+1))/(1-q^2)^3 := by
  have hq2 : q^2 < 1 := pow_lt_one₀ hq hq1 (by decide)
  have hn : ‖q^2‖ < 1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg q)]
    exact hq2
  let A := 2*q^(2*(N+1))/(1-q^2)^2
  have hg : HasSum (fun n : ℕ => A*(q^2)^n) (2*q^(2*(N+1))/(1-q^2)^3) := by
    convert! (hasSum_geometric_moment_zero (q^2) hn).mul_left A using 1
    dsimp only [A]
    field_simp [ne_of_gt (sub_pos.mpr hq2)]
  have hmajor (n : ℕ) : weierstrassHalfPeriodTerm q (n+N) ≤ A*(q^2)^n := by
    calc
      _ ≤ 2*q^(2*(n+N+1))/(1-q^2)^2 := term_majorant q hq hq1 (n+N)
      _ = _ := by
        rw [show 2*(n+N+1) = 2*(N+1)+2*n by omega]
        simp only [pow_add,pow_mul,A]
        ring
  have hsTail := Summable.of_nonneg_of_le
    (fun n => term_nonneg q hq (n+N)) hmajor hg.summable
  refine ⟨hsTail, ?_⟩
  simpa only [hg.tsum_eq] using hsTail.tsum_le_tsum hmajor hg.summable

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem lemniscate_frequency_bounds :
    Contains ⟨frequencyLower,frequencyUpper⟩ lemniscateFrequencySquared := by
  let q := Real.exp (-Real.pi)
  let l : ℝ := nomeLower
  let u : ℝ := nomeUpper
  let S := ∑' n : ℕ, weierstrassHalfPeriodTerm q n
  let Lh := ∑ n ∈ range 7, lowerTerm l u n
  let Uh := ∑ n ∈ range 7, upperTerm l u n
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hl0 : 0 ≤ l := by norm_num [l,nomeLower]
  have hu0 : 0 ≤ u := by norm_num [u,nomeUpper]
  have hu1 : u < 1 := by norm_num [u,nomeUpper]
  have hq : l ≤ q ∧ q ≤ u := refined_nome_bounds
  have hq1 : q < 1 := hq.2.trans_lt hu1
  have hs : Summable (weierstrassHalfPeriodTerm q) := by
    simpa only [Nat.add_zero] using (series_tail q hq0 hq1 0).1
  have hS0 : 0 ≤ S := tsum_nonneg (term_nonneg q hq0)
  have hhL : Lh ≤ ∑ n ∈ range 7, weierstrassHalfPeriodTerm q n :=
    sum_le_sum (fun n _ => (term_interval l q u hl0 hq.1 hq.2 hu1 n).1)
  have hhU : (∑ n ∈ range 7, weierstrassHalfPeriodTerm q n) ≤ Uh :=
    sum_le_sum (fun n _ => (term_interval l q u hl0 hq.1 hq.2 hu1 n).2)
  have hLh0 : 0 ≤ Lh := sum_nonneg (fun n _ => by dsimp only [lowerTerm]; positivity)
  have hloS : Lh ≤ S :=
    hhL.trans (hs.sum_le_tsum (range 7) (fun n _ => term_nonneg q hq0 n))
  have hqu2 : q^2 ≤ u^2 := pow_le_pow_left₀ hq0 hq.2 2
  have hu2 : u^2 < 1 := pow_lt_one₀ hu0 hu1 (by decide)
  have htail : (∑' n : ℕ, weierstrassHalfPeriodTerm q (n+7)) ≤
      2*u^16/(1-u^2)^3 := by
    apply (series_tail q hq0 hq1 7).2.trans
    exact div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hq.2 16) (by norm_num))
      (by positivity)
      (pow_le_pow_left₀ (sub_nonneg.mpr hu2.le) (sub_le_sub_left hqu2 1) 3)
  have hhiS : S ≤ Uh+2*u^16/(1-u^2)^3 := by
    calc
      S = (∑ n ∈ range 7, weierstrassHalfPeriodTerm q n) +
        (∑' n : ℕ, weierstrassHalfPeriodTerm q (n+7)) := (hs.sum_add_tsum_nat_add 7).symm
      _ ≤ _ := add_le_add hhU htail
  constructor
  · change (frequencyLower:ℝ) ≤ 3/(4*(1+12*S))
    calc
      _ ≤ 3/(4*(1+12*(Uh+2*u^16/(1-u^2)^3))) := by
        dsimp only [Uh,l,u]
        norm_num [frequencyLower,upperTerm,nomeLower,nomeUpper,sum_range_succ]
      _ ≤ _ := div_le_div₀ (by norm_num) le_rfl (by positivity) (by linarith)
  · change 3/(4*(1+12*S)) ≤ (frequencyUpper:ℝ)
    calc
      _ ≤ 3/(4*(1+12*Lh)) :=
        div_le_div₀ (by norm_num) le_rfl (by positivity) (by linarith)
      _ ≤ _ := by
        dsimp only [Lh,l,u]
        norm_num [frequencyUpper,lowerTerm,nomeLower,nomeUpper,sum_range_succ]

end

end Lemniscate.CoarseArithmetic
