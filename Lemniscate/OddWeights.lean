import Lemniscate.OddPolynomialSemantics

/-! Positive real weights for all odd Fourier rows, with both sign branches,
the common upper bound used in omitted columns, and the opposite-branch ratio.
They are evaluations of the exact coefficient lists used by the certificates. -/
namespace Lemniscate.OddArithmetic
open CoarseArithmetic

noncomputable def oddWeight (n : ℤ) (α : ℝ) : ℝ := realEval (weight n) α
noncomputable def oddPositiveBase (α : ℝ) : ℝ := 2/25-(3/25)*α+(2/25)*α^2
noncomputable def oddNegativeBase (α : ℝ) : ℝ := 2/25+α^2/20
noncomputable def oddWeightBase (n : ℤ) (α : ℝ) : ℝ :=
  if 0 < n then oddPositiveBase α else oddNegativeBase α

theorem odd_positive_base_bounds (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    1/25 ≤ oddPositiveBase α ∧ oddPositiveBase α ≤ 2/25 := by
  unfold oddPositiveBase
  constructor
  · nlinarith [mul_nonneg_of_nonpos_of_nonpos (by linarith : α-1/2 ≤ 0)
      (by linarith : α-1 ≤ 0)]
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos hα (by linarith : α-3/2 ≤ 0)]

theorem odd_negative_base_bounds (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    2/25 ≤ oddNegativeBase α ∧ oddNegativeBase α ≤ 37/400 := by
  unfold oddNegativeBase
  constructor
  · nlinarith [sq_nonneg α]
  · nlinarith [mul_nonneg hα (by linarith : 0 ≤ 1/2-α)]

theorem odd_weight_base_bounds (n : ℤ) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    1/25 ≤ oddWeightBase n α ∧ oddWeightBase n α ≤ 1/10 := by
  have hp := odd_positive_base_bounds α hα hα'
  have hm := odd_negative_base_bounds α hα hα'
  unfold oddWeightBase
  split_ifs <;> constructor <;> linarith

theorem odd_weight_base_ratio (n m : ℤ) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    oddWeightBase n α ≤ (37/16)*oddWeightBase m α := by
  have hp := odd_positive_base_bounds α hα hα'
  have hm := odd_negative_base_bounds α hα hα'
  unfold oddWeightBase
  split_ifs <;> nlinarith

theorem odd_weight_one (α : ℝ) : oddWeight 1 α = 1 := by
  norm_num [oddWeight, weight, realEval_const]

theorem odd_weight_neg_one (α : ℝ) : oddWeight (-1) α = 1-(8/5)*α+(4/5)*α^2 := by
  norm_num [oddWeight, weight, realEval_quadratic]
  ring

theorem odd_weight_three (α : ℝ) : oddWeight 3 α = 1/2-(1/2)*α+(3/25)*α^2 := by
  norm_num [oddWeight, weight, realEval_quadratic]
  ring

theorem odd_weight_neg_three (α : ℝ) : oddWeight (-3) α = 1/2+(3/10)*α^2 := by
  norm_num [oddWeight, weight, realEval_quadratic]

theorem odd_weight_other (n : ℤ) (α : ℝ)
    (h1 : n ≠ 1) (hm1 : n ≠ -1) (h3 : n ≠ 3) (hm3 : n ≠ -3) :
    oddWeight n α = if n.natAbs = 5 then oddWeightBase n α else
      (3/25:ℝ)*(a:ℝ)^((n.natAbs-7)/2)*oddWeightBase n α := by
  unfold oddWeight weight
  simp only [if_neg h1, if_neg hm1, if_neg h3, if_neg hm3]
  by_cases hp : 0 < n <;> by_cases ha : n.natAbs = 5 <;>
    norm_num [hp, ha, realEval_scale, realEval_quadratic, oddWeightBase,
      oddPositiveBase, oddNegativeBase, Rat.cast_mul, Rat.cast_pow] <;> ring_nf <;> simp

theorem odd_weight_positive (n : ℤ) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    0 < oddWeight n α := by
  by_cases h1 : n = 1
  · subst n
    rw [odd_weight_one]
    norm_num
  by_cases hm1 : n = -1
  · subst n
    rw [odd_weight_neg_one]
    nlinarith [sq_nonneg α]
  by_cases h3 : n = 3
  · subst n
    rw [odd_weight_three]
    nlinarith [sq_nonneg α]
  by_cases hm3 : n = -3
  · subst n
    rw [odd_weight_neg_three]
    nlinarith [sq_nonneg α]
  rw [odd_weight_other n α h1 hm1 h3 hm3]
  have hb : 0 < oddWeightBase n α := lt_of_lt_of_le (by norm_num)
    (odd_weight_base_bounds n α hα hα').1
  split_ifs
  · exact hb
  · have ha : 0 < (a:ℝ) := by norm_num [a]
    positivity

theorem odd_weight_high (n : ℤ) (α : ℝ) (hn : 7 ≤ n.natAbs) :
    oddWeight n α = (3/25:ℝ)*(a:ℝ)^((n.natAbs-7)/2)*oddWeightBase n α := by
  have h1 : n ≠ 1 := by intro h; subst n; norm_num at hn
  have hm1 : n ≠ -1 := by intro h; subst n; norm_num at hn
  have h3 : n ≠ 3 := by intro h; subst n; norm_num at hn
  have hm3 : n ≠ -3 := by intro h; subst n; norm_num at hn
  rw [odd_weight_other n α h1 hm1 h3 hm3, if_neg (by omega)]

theorem odd_weight_high_upper (n : ℤ) (α : ℝ) (hn : 7 ≤ n.natAbs)
    (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    oddWeight n α ≤ (3/250:ℝ)*(a:ℝ)^((n.natAbs-7)/2) := by
  rw [odd_weight_high n α hn]
  calc
    _ ≤ ((3/25:ℝ)*(a:ℝ)^((n.natAbs-7)/2))*(1/10) :=
      mul_le_mul_of_nonneg_left (odd_weight_base_bounds n α hα hα').2
        (by
          have ha : 0 ≤ (a:ℝ) := by norm_num [a]
          exact mul_nonneg (by norm_num) (pow_nonneg ha _))
    _ = _ := by ring

theorem odd_zero_weighted_low_margin (i : Fin 12) :
    5*oddWeight (lowIndex i) 0 < realEval (rowPolynomial (lowIndex i)) 0 := by
  have hp := odd_weight_positive (lowIndex i) 0 (by norm_num) (by norm_num)
  have he := odd_zero_rows_real i
  rw [oddWeight, realEval_zero] at hp
  rw [oddWeight, realEval_zero, realEval_zero]
  exact (lt_div_iff₀ hp).mp he

end Lemniscate.OddArithmetic
