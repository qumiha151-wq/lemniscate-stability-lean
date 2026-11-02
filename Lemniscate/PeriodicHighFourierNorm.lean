import Lemniscate.PeriodicHighFourierDuality
import Lemniscate.PeriodicAngularH4Norm

/-! Bound the high-frequency homogeneous H^{-2} square by the L2 norm.
This estimates the action on the already controlled finite-vector tails. -/
namespace Lemniscate
open Complex MeasureTheory
variable (T : ℝ) [Fact (0 < T)]

theorem complex_norm_add_square_young (a b : ℂ) (p : ℝ) (hp : 0 < p) :
    ‖a+b‖^2 ≤ (1+p)*‖a‖^2+(1+p⁻¹)*‖b‖^2 := by
  have hs := pow_le_pow_left₀ (norm_nonneg (a+b)) (norm_add_le a b) 2
  have hm := mul_le_mul_of_nonneg_left hs hp.le
  have heq : p*((1+p)*‖a‖^2+(1+p⁻¹)*‖b‖^2) =
      p*(‖a‖+‖b‖)^2+(p*‖a‖-‖b‖)^2 := by
    field_simp [ne_of_gt hp]
    ring
  apply (mul_le_mul_iff_right₀ hp).mp
  rw [heq]
  exact hm.trans (le_add_of_nonneg_right (sq_nonneg _))

theorem circle_high_fourier_square_bound (g : CircleL2 T) (S : Set ℤ)
    [DecidablePred (fun n => n ∈ S)] (hS : ∀ n ∈ S, 32 ≤ |(n:ℝ)|) :
    Summable (fun n : ℤ => if n ∈ S then ‖fourierCoeff g n‖^2/(n:ℝ)^4 else 0) ∧
    (∑' n : ℤ, if n ∈ S then ‖fourierCoeff g n‖^2/(n:ℝ)^4 else 0) ≤ ‖g‖^2/32^4 := by
  classical
  have hp (n : ℤ) (hn : n ∈ S) : (32:ℝ)^4 ≤ (n:ℝ)^4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 32) (hS n hn) 4
    have heq : |(n:ℝ)|^4 = (n:ℝ)^4 := by
      calc
        _ = (|(n:ℝ)|^2)^2 := by ring
        _ = ((n:ℝ)^2)^2 := by rw [sq_abs]
        _ = _ := by ring
    simpa only [heq] using h
  have hn (n : ℤ) : 0 ≤ if n ∈ S then ‖fourierCoeff g n‖^2/(n:ℝ)^4 else 0 := by
    split_ifs <;> positivity
  have hb (n : ℤ) : (if n ∈ S then ‖fourierCoeff g n‖^2/(n:ℝ)^4 else 0) ≤
      ‖fourierCoeff g n‖^2/(32:ℝ)^4 := by
    by_cases hns : n ∈ S
    · rw [if_pos hns]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (hp n hns)
    · rw [if_neg hns]
      positivity
  have hR := (circle_fourier_square_summable T g).div_const ((32:ℝ)^4)
  have hL := Summable.of_nonneg_of_le hn hb hR
  have h := hL.tsum_le_tsum hb hR
  refine ⟨hL,?_⟩
  simpa only [tsum_div_const, ← circle_norm_sq_fourier] using h

theorem circle_high_fourier_add_square_bound (f g : CircleL2 T) (S : Set ℤ)
    [DecidablePred (fun n => n ∈ S)] (hS : ∀ n ∈ S, 32 ≤ |(n:ℝ)|)
    (p : ℝ) (hp : 0 < p) :
    (∑' n : ℤ, if n ∈ S then ‖fourierCoeff (f+g) n‖^2/(n:ℝ)^4 else 0) ≤
      (1+p)*(∑' n : ℤ, if n ∈ S then ‖fourierCoeff f n‖^2/(n:ℝ)^4 else 0)+
      (1+p⁻¹)*(∑' n : ℤ, if n ∈ S then ‖fourierCoeff g n‖^2/(n:ℝ)^4 else 0) := by
  have hf := (circle_high_fourier_square_bound T f S hS).1
  have hg := (circle_high_fourier_square_bound T g S hS).1
  have hfg := (circle_high_fourier_square_bound T (f+g) S hS).1
  have hRf := hf.mul_left (1+p)
  have hRg := hg.mul_left (1+p⁻¹)
  have hb (n : ℤ) : (if n ∈ S then ‖fourierCoeff (f+g) n‖^2/(n:ℝ)^4 else 0) ≤
      (1+p)*(if n ∈ S then ‖fourierCoeff f n‖^2/(n:ℝ)^4 else 0)+
      (1+p⁻¹)*(if n ∈ S then ‖fourierCoeff g n‖^2/(n:ℝ)^4 else 0) := by
    by_cases hn : n ∈ S
    · simp only [if_pos hn,circle_fourierCoeff_add]
      have h := div_le_div_of_nonneg_right
        (complex_norm_add_square_young (fourierCoeff f n) (fourierCoeff g n) p hp)
        (by positivity : 0 ≤ (n:ℝ)^4)
      simpa only [add_div,mul_div_assoc] using h
    · simp only [if_neg hn,mul_zero,add_zero,le_refl]
  have h := hfg.tsum_le_tsum hb (hRf.add hRg)
  simpa only [hRf.tsum_add hRg,tsum_mul_left] using h

theorem circle_high_action_on_small_h4 (A : circleH4Domain T →ₗ[ℂ] CircleL2 T)
    (hA : ∀ f, ‖A f‖ ≤ 200*circleAngularH4Norm T f)
    (f : circleH4Domain T) (hf : circleAngularH4Norm T f ≤ 1/10000)
    (S : Set ℤ) [DecidablePred (fun n => n ∈ S)]
    (hS : ∀ n ∈ S, 32 ≤ |(n:ℝ)|) :
    (∑' n : ℤ, if n ∈ S then ‖fourierCoeff (A f) n‖^2/(n:ℝ)^4 else 0) ≤ (1/51200:ℝ)^2 := by
  classical
  have hAf : ‖A f‖ ≤ (1/50:ℝ) := by linarith only [hA f,hf]
  have hsq := pow_le_pow_left₀ (norm_nonneg (A f)) hAf 2
  calc
    _ ≤ ‖A f‖^2/(32:ℝ)^4 := (circle_high_fourier_square_bound T (A f) S hS).2
    _ ≤ (1/50:ℝ)^2/(32:ℝ)^4 := div_le_div_of_nonneg_right hsq (by norm_num)
    _ = _ := by norm_num

end Lemniscate
