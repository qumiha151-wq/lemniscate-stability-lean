import Lemniscate.IntervalMatrices

/-! Intervals with a common denominator. Closed matrix comparisons use only
integer arithmetic; the soundness proof below relates them to real intervals.
Products are rounded outwards to twelve decimal places. -/
namespace Lemniscate.CoarseArithmetic

structure IntegerInterval where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq

def integerDenominator : ℤ := 1000000000000000000
def integerRoundingStep : ℤ := 1000000

def IntegerInterval.toInterval (I : IntegerInterval) : Interval :=
  ⟨(I.lo:ℚ)/integerDenominator, (I.hi:ℚ)/integerDenominator⟩

def IntegerEncloses (I J : IntegerInterval) : Prop := I.lo ≤ J.lo ∧ J.hi ≤ I.hi
instance (I J : IntegerInterval) : Decidable (IntegerEncloses I J) :=
  inferInstanceAs (Decidable (I.lo ≤ J.lo ∧ J.hi ≤ I.hi))

def integerInput (I : Interval) : IntegerInterval :=
  ⟨⌊I.lo*(integerDenominator:ℚ)⌋, ⌈I.hi*(integerDenominator:ℚ)⌉⟩

theorem integer_input_encloses (I : Interval) : Encloses (integerInput I).toInterval I := by
  have hd : (0:ℚ) < integerDenominator := by norm_num [integerDenominator]
  constructor
  · exact (div_le_iff₀ hd).mpr (Int.floor_le _)
  · exact (le_div_iff₀ hd).mpr (Int.le_ceil _)

theorem integer_input_sound (I : Interval) (x : ℝ) (hx : Contains I x) :
    Contains (integerInput I).toInterval x :=
  hx.mono (integer_input_encloses I).1 (integer_input_encloses I).2

def integerPoint (q : ℚ) : IntegerInterval := integerInput (point q)

theorem integer_point_sound (q : ℚ) : Contains (integerPoint q).toInterval (q:ℝ) :=
  integer_input_sound _ _ (point_sound q)

def integerAdd (I J : IntegerInterval) : IntegerInterval := ⟨I.lo+J.lo,I.hi+J.hi⟩
def integerNeg (I : IntegerInterval) : IntegerInterval := ⟨-I.hi,-I.lo⟩
def integerMul (I J : IntegerInterval) : IntegerInterval :=
  let l := min (min (I.lo*J.lo) (I.lo*J.hi)) (min (I.hi*J.lo) (I.hi*J.hi))
  let u := max (max (I.lo*J.lo) (I.lo*J.hi)) (max (I.hi*J.lo) (I.hi*J.hi))
  ⟨l/(integerDenominator*integerRoundingStep)*integerRoundingStep,
    -((-u)/(integerDenominator*integerRoundingStep))*integerRoundingStep⟩

theorem integer_denominator_pos : 0 < integerDenominator := by decide
theorem integer_rounding_step_pos : 0 < integerRoundingStep := by decide

theorem integer_encloses_sound (I J : IntegerInterval) (h : IntegerEncloses I J) :
    Encloses I.toInterval J.toInterval := by
  have hd : (0:ℚ) < integerDenominator := by exact_mod_cast integer_denominator_pos
  constructor
  · exact div_le_div_of_nonneg_right (by exact_mod_cast h.1) hd.le
  · exact div_le_div_of_nonneg_right (by exact_mod_cast h.2) hd.le

theorem integer_add_to_interval (I J : IntegerInterval) :
    (integerAdd I J).toInterval = add I.toInterval J.toInterval := by
  apply congrArg₂ Interval.mk <;>
    simp only [IntegerInterval.toInterval, integerAdd, Int.cast_add, add_div]

theorem integer_neg_sound (I : IntegerInterval) (x : ℝ) (hx : Contains I.toInterval x) :
    Contains (integerNeg I).toInterval (-x) := by
  constructor
  · simpa only [IntegerInterval.toInterval, integerNeg, Int.cast_neg, neg_div,
      Rat.cast_neg] using neg_le_neg hx.2
  · simpa only [IntegerInterval.toInterval, integerNeg, Int.cast_neg, neg_div,
      Rat.cast_neg] using neg_le_neg hx.1

private theorem integer_product_lower (l a b : ℤ) (h : l*integerDenominator ≤ a*b) :
    (l:ℚ)/integerDenominator ≤ (a:ℚ)/integerDenominator*((b:ℚ)/integerDenominator) := by
  have hd : (0:ℚ) < integerDenominator := by exact_mod_cast integer_denominator_pos
  have hc : (l:ℚ)*(integerDenominator:ℚ) ≤ (a:ℚ)*(b:ℚ) := by exact_mod_cast h
  calc
    _ ≤ ((a:ℚ)*(b:ℚ)/integerDenominator)/integerDenominator :=
      div_le_div_of_nonneg_right ((le_div_iff₀ hd).mpr hc) hd.le
    _ = _ := by ring

private theorem integer_product_upper (u a b : ℤ) (h : a*b ≤ u*integerDenominator) :
    (a:ℚ)/integerDenominator*((b:ℚ)/integerDenominator) ≤ (u:ℚ)/integerDenominator := by
  have hd : (0:ℚ) < integerDenominator := by exact_mod_cast integer_denominator_pos
  have hc : (a:ℚ)*(b:ℚ) ≤ (u:ℚ)*(integerDenominator:ℚ) := by exact_mod_cast h
  calc
    _ = ((a:ℚ)*(b:ℚ)/integerDenominator)/integerDenominator := by ring
    _ ≤ _ := div_le_div_of_nonneg_right ((div_le_iff₀ hd).mpr hc) hd.le

theorem integer_mul_encloses (I J : IntegerInterval) :
    Encloses (integerMul I J).toInterval (mul I.toInterval J.toInterval) := by
  let l := min (min (I.lo*J.lo) (I.lo*J.hi)) (min (I.hi*J.lo) (I.hi*J.hi))
  let u := max (max (I.lo*J.lo) (I.lo*J.hi)) (max (I.hi*J.lo) (I.hi*J.hi))
  have hd := ne_of_gt (mul_pos integer_denominator_pos integer_rounding_step_pos)
  have hl : (integerMul I J).lo*integerDenominator ≤ l := by
    have h := Int.ediv_mul_le l hd
    change (l/(integerDenominator*integerRoundingStep)*integerRoundingStep)*integerDenominator ≤ l
    calc
      _ = (l/(integerDenominator*integerRoundingStep))*(integerDenominator*integerRoundingStep) := by ring
      _ ≤ l := h
  have hu : u ≤ (integerMul I J).hi*integerDenominator := by
    have h := Int.ediv_mul_le (-u) hd
    change u ≤ (-((-u)/(integerDenominator*integerRoundingStep))*integerRoundingStep)*integerDenominator
    calc
      u = -(-u) := by ring
      _ ≤ -(((-u)/(integerDenominator*integerRoundingStep))*(integerDenominator*integerRoundingStep)) := neg_le_neg h
      _ = _ := by ring
  have hll := integer_product_lower _ _ _ (hl.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hlh := integer_product_lower _ _ _ (hl.trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hhl := integer_product_lower _ _ _ (hl.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hhh := integer_product_lower _ _ _ (hl.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hll' := integer_product_upper _ _ _ (((le_max_left _ _).trans (le_max_left _ _)).trans hu)
  have hlh' := integer_product_upper _ _ _ (((le_max_right _ _).trans (le_max_left _ _)).trans hu)
  have hhl' := integer_product_upper _ _ _ (((le_max_left _ _).trans (le_max_right _ _)).trans hu)
  have hhh' := integer_product_upper _ _ _ (((le_max_right _ _).trans (le_max_right _ _)).trans hu)
  exact ⟨le_min (le_min hll hlh) (le_min hhl hhh),
    max_le (max_le hll' hlh') (max_le hhl' hhh')⟩

theorem integer_mul_sound (I J : IntegerInterval) (x y : ℝ)
    (hI : Contains I.toInterval x) (hJ : Contains J.toInterval y) :
    Contains (integerMul I J).toInterval (x*y) :=
  (mul_sound _ _ _ _ hI hJ).mono (integer_mul_encloses I J).1 (integer_mul_encloses I J).2

end Lemniscate.CoarseArithmetic
