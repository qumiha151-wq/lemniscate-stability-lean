import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A rational enclosure for the exact angle in the winding-one closure equation. -/
namespace SolitonClassification.Rotating.IntegerTarget
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

private def precision : ℕ := 10^150
private def down : ℕ → ℕ
  | 0 => 0
  | n+1 => Nat.sqrt ((2*precision+down n)*precision)
private def up : ℕ → ℕ
  | 0 => 0
  | n+1 => Nat.sqrt ((2*precision+up n)*precision)+1

private theorem sqrt_enclosure (n:ℕ) :
    (down n:ℝ)/precision ≤ Real.sqrtTwoAddSeries 0 n ∧
    Real.sqrtTwoAddSeries 0 n ≤ (up n:ℝ)/precision := by
  have hp : 0 < (precision:ℝ) := by norm_num [precision]
  induction n with
  | zero => simp [down,up,Real.sqrtTwoAddSeries]
  | succ n ih =>
    have low : (down (n+1):ℝ)^2 ≤ (2*(precision:ℝ)+down n)*precision := by
      exact_mod_cast Nat.sqrt_le' ((2*precision+down n)*precision)
    have high : (2*(precision:ℝ)+up n)*precision ≤ (up (n+1):ℝ)^2 := by
      exact_mod_cast (Nat.lt_succ_sqrt' ((2*precision+up n)*precision)).le
    constructor
    · rw [Real.sqrtTwoAddSeries]
      apply le_trans _ (Real.sqrt_le_sqrt (add_le_add_right ih.1 2))
      apply Real.le_sqrt_of_sq_le
      rw [div_pow]
      apply (div_le_iff₀ (pow_pos hp 2)).mpr
      calc
        _ ≤ (2*(precision:ℝ)+down n)*precision := low
        _ = _ := by field_simp [hp.ne']
    · rw [Real.sqrtTwoAddSeries]
      apply (Real.sqrt_le_sqrt (add_le_add_right ih.2 2)).trans
      apply (Real.sqrt_le_left (by positivity)).mpr
      rw [div_pow]
      apply (le_div_iff₀ (pow_pos hp 2)).mpr
      calc
        _ = (2*(precision:ℝ)+up n)*precision := by field_simp [hp.ne']
        _ ≤ _ := high

def piFloor : ℚ := 314159265358979323846264338327950288419716939937510582097/10^56

theorem pi_lower : (piFloor:ℝ)<Real.pi := by
  apply Real.pi_lower_bound_start 100
  simp only [Nat.cast_zero,Nat.cast_one,zero_div]
  apply (sqrt_enclosure 100).2.trans
  have h : (up 100:ℚ)/precision ≤ 2-(piFloor/(2:ℚ)^101)^2 := by decide +kernel
  have hr := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hr ⊢
  exact hr

theorem pi_upper : Real.pi < ((piFloor+(1:ℚ)/10^56:ℚ):ℝ) := by
  apply Real.pi_upper_bound_start 100
  · simp only [Nat.cast_zero,Nat.cast_one,zero_div]
    apply le_trans _ (sqrt_enclosure 100).1
    have h : (2:ℚ)-((piFloor+1/10^56-1/(4:ℚ)^100)/(2:ℚ)^101)^2 ≤ (down 100:ℚ)/precision := by decide +kernel
    have hr := (Rat.cast_le (K := ℝ)).mpr h
    push_cast at hr ⊢
    exact hr
  · norm_num [piFloor]
end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.pi_lower
#print axioms SolitonClassification.Rotating.IntegerTarget.pi_upper
