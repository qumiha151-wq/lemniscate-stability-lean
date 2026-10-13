import Lemniscate.Algebra
import Lemniscate.CoarseArithmetic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Rat.Cast.Order

/-! Analytic meaning of the first three geometric tail formulas used in the
row certificates. `HasSum` proves both convergence and the stated exact value. -/
namespace Lemniscate
open CoarseArithmetic

theorem hasSum_geometric_moment_zero (z : ℝ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z^n) (1/(1-z)) := by
  simpa only [one_div] using hasSum_geometric_of_norm_lt_one hz

theorem hasSum_geometric_moment_one (z : ℝ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (n:ℝ)*z^n) (z/(1-z)^2) :=
  hasSum_coe_mul_geometric_of_norm_lt_one hz

theorem hasSum_geometric_moment_two (z : ℝ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (n:ℝ)^2*z^n) (z*(1+z)/(1-z)^3) := by
  have hden : 1-z ≠ 0 := by
    have hlt : z < 1 := lt_of_le_of_lt (le_abs_self z) hz
    linarith
  have hs := summable_pow_mul_geometric_of_norm_lt_one 2 hz
  let s := ∑' n : ℕ, (n:ℝ)^2*z^n
  have h0 := hasSum_geometric_moment_zero z hz
  have h1 := hasSum_geometric_moment_one z hz
  have hnext : HasSum (fun n : ℕ => ((n:ℝ)+1)^2*z^n)
      (s+2*(z/(1-z)^2)+1/(1-z)) := by
    convert! (hs.hasSum.add (h1.mul_left 2)).add h0 using 1
    ext n
    ring
  have heq : s = z*(s+2*(z/(1-z)^2)+1/(1-z)) := by
    calc
      s = ∑' n : ℕ, ((n+1:ℕ):ℝ)^2*z^(n+1) := by
        simpa only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add]
          using hs.tsum_eq_zero_add
      _ = _ := by
        convert! (hnext.mul_left z).tsum_eq using 1
        congr 1
        ext n
        simp only [Nat.cast_add, Nat.cast_one, pow_succ]
        ring
  have hsval : s = z*(1+z)/(1-z)^3 := by
    have hf : (1-z)*s = z*(2*(z/(1-z)^2)+1/(1-z)) := by linarith
    field_simp [hden] at hf ⊢
    nlinarith [hf]
  simpa only [← hsval] using hs.hasSum

theorem hasSum_geometric_moment_three (z : ℝ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (n:ℝ)^3*z^n) (z*(1+4*z+z^2)/(1-z)^4) := by
  have hden : 1-z ≠ 0 := by
    have hlt : z < 1 := lt_of_le_of_lt (le_abs_self z) hz
    linarith
  have hs := summable_pow_mul_geometric_of_norm_lt_one 3 hz
  let s := ∑' n : ℕ, (n:ℝ)^3*z^n
  have h0 := hasSum_geometric_moment_zero z hz
  have h1 := hasSum_geometric_moment_one z hz
  have h2 := hasSum_geometric_moment_two z hz
  have hnext : HasSum (fun n : ℕ => ((n:ℝ)+1)^3*z^n)
      (s+3*(z*(1+z)/(1-z)^3)+3*(z/(1-z)^2)+1/(1-z)) := by
    convert! ((hs.hasSum.add (h2.mul_left 3)).add (h1.mul_left 3)).add h0 using 1
    ext n
    ring
  have heq : s = z*(s+3*(z*(1+z)/(1-z)^3)+3*(z/(1-z)^2)+1/(1-z)) := by
    calc
      s = ∑' n : ℕ, ((n+1:ℕ):ℝ)^3*z^(n+1) := by
        simpa only [Nat.cast_zero, zero_pow (by decide : 3 ≠ 0), zero_mul, zero_add]
          using hs.tsum_eq_zero_add
      _ = _ := by
        convert! (hnext.mul_left z).tsum_eq using 1
        congr 1
        ext n
        simp only [Nat.cast_add, Nat.cast_one, pow_succ]
        ring
  have hsval : s = z*(1+4*z+z^2)/(1-z)^4 := by
    have hf : (1-z)*s = z*(3*(z*(1+z)/(1-z)^3)+3*(z/(1-z)^2)+1/(1-z)) := by
      linarith
    field_simp [hden] at hf ⊢
    nlinarith [hf]
  simpa only [← hsval] using hs.hasSum

theorem tail1_sound (z : ℚ) (hz : ‖(z:ℝ)‖ < 1) (L : ℕ) :
    HasSum (fun n : ℕ => ((n+L:ℕ):ℝ)*(z:ℝ)^(n+L)) (tail1 z L : ℝ) := by
  convert! (((hasSum_geometric_moment_zero z hz).mul_left (L:ℝ)).add
    (hasSum_geometric_moment_one z hz)).mul_left ((z:ℝ)^L) using 1
  · ext n
    simp only [Nat.cast_add, pow_add]
    ring
  · norm_num [tail1, moment] <;> ring

theorem tail2_sound (z : ℚ) (hz : ‖(z:ℝ)‖ < 1) (L : ℕ) :
    HasSum (fun n : ℕ => ((n+L:ℕ):ℝ)^2*(z:ℝ)^(n+L)) (tail2 z L : ℝ) := by
  convert! ((((hasSum_geometric_moment_zero z hz).mul_left ((L:ℝ)^2)).add
    ((hasSum_geometric_moment_one z hz).mul_left (2*(L:ℝ)))).add
    (hasSum_geometric_moment_two z hz)).mul_left ((z:ℝ)^L) using 1
  · ext n
    simp only [Nat.cast_add, pow_add]
    ring
  · norm_num [tail2, moment] <;> ring

theorem tail3_sound (z : ℚ) (hz : ‖(z:ℝ)‖ < 1) (L : ℕ) :
    HasSum (fun n : ℕ => ((n+L:ℕ):ℝ)^3*(z:ℝ)^(n+L)) (tail3 z L : ℝ) := by
  convert! (((((hasSum_geometric_moment_zero z hz).mul_left ((L:ℝ)^3)).add
    ((hasSum_geometric_moment_one z hz).mul_left (3*(L:ℝ)^2))).add
    ((hasSum_geometric_moment_two z hz).mul_left (3*(L:ℝ)))).add
    (hasSum_geometric_moment_three z hz)).mul_left ((z:ℝ)^L) using 1
  · ext n
    simp only [Nat.cast_add, pow_add]
    ring
  · norm_num [tail3, moment] <;> ring

end Lemniscate
