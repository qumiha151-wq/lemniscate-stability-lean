import Lemniscate.PeriodicFourierCoupling
import Lemniscate.PeriodicBlochHighFrequency

/-! The homogeneous H^{-2}-H^2 pairing bound on a high-frequency set.
Summability follows from L2 Parseval and the actual H4 input domain. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

theorem circle_high_fourier_duality (g : CircleL2 T) (y : circleH4Domain T)
    (S : Set ℤ) [DecidablePred (fun n => n ∈ S)]
    (hS : ∀ n ∈ S, 32 ≤ |(n:ℝ)|)
    (hy : ∀ n ∉ S, fourierCoeff (y:CircleL2 T) n = 0) :
    ‖inner ℂ g (y:CircleL2 T)‖^2 ≤
      (∑' n : ℤ, if n ∈ S then ‖fourierCoeff g n‖^2/(n:ℝ)^4 else 0)*
        (∑' n : ℤ, (n:ℝ)^4*‖fourierCoeff (y:CircleL2 T) n‖^2) := by
  classical
  let ω : ℤ → ℝ := fun n => max 1 ((n:ℝ)^4)
  have hw (n : ℤ) : 1 ≤ ω n := by
    dsimp only [ω]
    exact le_max_left (1:ℝ) ((n:ℝ)^4)
  have hwpos (n : ℤ) : 0 < ω n := lt_of_lt_of_le (by norm_num) (hw n)
  have hp (n : ℤ) (hn : n ∈ S) : 1 ≤ (n:ℝ)^4 := by
    have habs : 1 ≤ |(n:ℝ)| := (by norm_num : (1:ℝ) ≤ 32).trans (hS n hn)
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) habs 4
    have heq : |(n:ℝ)|^4 = (n:ℝ)^4 := by
      calc
        _ = (|(n:ℝ)|^2)^2 := by ring
        _ = ((n:ℝ)^2)^2 := by rw [sq_abs]
        _ = _ := by ring
    simpa only [one_pow, heq] using h
  have hc0 (n : ℤ) : 0 ≤ if n ∈ S then ‖fourierCoeff g n‖^2/ω n else 0 := by
    split_ifs <;> positivity
  have hc1 (n : ℤ) : (if n ∈ S then ‖fourierCoeff g n‖^2/ω n else 0) ≤ ‖fourierCoeff g n‖^2 := by
    split_ifs
    · apply (div_le_iff₀ (hwpos n)).mpr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hw n) (sq_nonneg ‖fourierCoeff g n‖)
    · exact sq_nonneg _
  have hCs := Summable.of_nonneg_of_le hc0 hc1 (circle_fourier_square_summable T g)
  have hCeq (n : ℤ) :
      (∑ _i : Unit, ‖if n ∈ S then conj (fourierCoeff g n) else 0‖^2/((1:ℝ)*ω n)) =
        (if n ∈ S then ‖fourierCoeff g n‖^2/ω n else 0) := by
    by_cases hn : n ∈ S <;> simp [hn]
  have hC : Summable (fun n : ℤ =>
      ∑ _i : Unit, ‖if n ∈ S then conj (fourierCoeff g n) else 0‖^2/((1:ℝ)*ω n)) := by
    simpa only [hCeq] using hCs
  have hWeq (n : ℤ) : ω n*‖fourierCoeff (y:CircleL2 T) n‖^2 =
      (n:ℝ)^4*‖fourierCoeff (y:CircleL2 T) n‖^2 := by
    by_cases hn : n ∈ S
    · simp only [ω, max_eq_right (hp n hn)]
    · simp only [hy n hn, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
  have hW : Summable (fun n : ℤ => ω n*‖fourierCoeff (y:CircleL2 T) n‖^2) := by
    simpa only [hWeq] using circle_fourier_fourth_weight_summable T y
  have hbound : ‖inner ℂ g (y:CircleL2 T)‖^2 ≤
      (∑' n : ℤ, ‖if n ∈ S then conj (fourierCoeff g n) else 0‖^2/ω n)*
        (∑' n : ℤ, ω n*‖fourierCoeff (y:CircleL2 T) n‖^2) := by
    simpa using circle_weighted_fourier_coupling T (fun _ : Unit => g)
      (fun _ : Unit => (1:ℂ)) (y:CircleL2 T) S hy (fun _ : Unit => (1:ℝ)) ω
      (by intro _; norm_num) hwpos hC hW
  refine hbound.trans_eq ?_
  congr 1
  · apply tsum_congr
    intro n
    by_cases hn : n ∈ S
    · simp only [if_pos hn, norm_conj, ω, max_eq_right (hp n hn)]
    · simp only [if_neg hn, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div]
  · exact tsum_congr hWeq

end Lemniscate
