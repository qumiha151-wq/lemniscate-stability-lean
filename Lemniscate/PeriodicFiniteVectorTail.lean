import Lemniscate.PeriodicApproximationBounds

/-! H4 bounds for the modes 22,...,30 of the actual finite auxiliary
vectors. Only their remaining five sine coefficients need to be estimated. -/
namespace Lemniscate.CoarseArithmetic

def finiteSineTailInterval (I : Fin 15 → Interval) (j : Fin 15) : Interval :=
  if 10 ≤ j.val then I j else point 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finite_vector_h4_tail_certificate :
    intervalL4 (finiteSineTailInterval rotationFiniteData) ≤ 1/10000 ∧
    intervalL4 (finiteSineTailInterval differenceFiniteData) ≤ 1/10000 := by
  constructor <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finite_vector_low_l1_certificate :
    (∑ j : Fin 10, absUpper (rotationFiniteData (Fin.castAdd 5 j))) ≤ 2 ∧
    (∑ j : Fin 10, absUpper (differenceFiniteData (Fin.castAdd 5 j))) ≤ 2 := by
  constructor <;> decide +kernel

end Lemniscate.CoarseArithmetic

namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleFiniteSineTail (v : Fin 15 → ℝ) : circleH4Domain T :=
  I • circleSineTrialH4 T 15 (fun j => ((if 10 ≤ j.val then v j else 0:ℝ):ℂ))

noncomputable def circleFiniteSineLow (v : Fin 15 → ℝ) : circleH4Domain T :=
  I • circleSineTrialH4 T 10 (fun j => (v (Fin.castAdd 5 j):ℂ))

theorem circle_finite_sine_low_tail (v : Fin 15 → ℝ) :
    I • circleSineTrialH4 T 15 (fun j => (v j:ℂ)) =
      circleFiniteSineLow T v+circleFiniteSineTail T v := by
  simp only [circleFiniteSineLow,circleFiniteSineTail,circleSineTrialH4]
  rw [Fin.sum_univ_add (a := 10) (b := 5),Fin.sum_univ_add (a := 10) (b := 5)]
  simp only [Fin.val_castAdd,Fin.val_natAdd,
    show ∀ j : Fin 10, ¬10 ≤ j.val by omega,
    show ∀ j : Fin 5, 10 ≤ 10+j.val by omega,if_false,if_true,
    Complex.ofReal_zero,zero_smul,Finset.sum_const_zero,zero_add,smul_add]

private theorem low_sine_l1_bound (I : Fin 15 → Interval) (v : Fin 15 → ℝ)
    (hv : ∀ j, Contains (I j) (v j)) :
    (∑ j : Fin 10, ‖(v (Fin.castAdd 5 j):ℂ)‖) ≤
      ((∑ j : Fin 10, absUpper (I (Fin.castAdd 5 j)):ℚ):ℝ) := by
  simp only [Rat.cast_sum,Complex.norm_real,Real.norm_eq_abs]
  apply Finset.sum_le_sum
  intro j _
  exact absUpper_sound _ _ (hv _)

theorem finite_vector_low_l1_bounds :
    (∑ j : Fin 10, ‖(rotationFiniteCoefficient (Fin.castAdd 5 j):ℂ)‖) ≤ 2 ∧
    (∑ j : Fin 10, ‖(finiteDifferenceCoefficient (Fin.castAdd 5 j):ℂ)‖) ≤ 2 := by
  constructor
  · exact (low_sine_l1_bound rotationFiniteData rotationFiniteCoefficient rotation_finite_data_sound).trans
      (by exact_mod_cast finite_vector_low_l1_certificate.1)
  · exact (low_sine_l1_bound differenceFiniteData finiteDifferenceCoefficient difference_finite_data_sound).trans
      (by exact_mod_cast finite_vector_low_l1_certificate.2)

private theorem finite_sine_tail_interval_bound (I : Fin 15 → Interval) (v : Fin 15 → ℝ)
    (hv : ∀ j, Contains (I j) (v j)) :
    circleAngularH4Norm T (circleFiniteSineTail T v) ≤
      (intervalL4 (finiteSineTailInterval I):ℝ) := by
  rw [circleFiniteSineTail, circle_angular_h4_norm_smul, Complex.norm_I, one_mul]
  apply circle_sine_interval_norm_le
  intro j
  by_cases hj : 10 ≤ j.val
  · simpa only [finiteSineTailInterval, if_pos hj] using hv j
  · simpa only [finiteSineTailInterval, if_neg hj, Rat.cast_zero] using point_sound 0

theorem circle_finite_vector_h4_tail_bounds :
    circleAngularH4Norm T (circleFiniteSineTail T rotationFiniteCoefficient) ≤ 1/10000 ∧
    circleAngularH4Norm T (circleFiniteSineTail T finiteDifferenceCoefficient) ≤ 1/10000 := by
  constructor
  · have hnum : (intervalL4 (finiteSineTailInterval rotationFiniteData):ℝ) ≤ ((1/10000:ℚ):ℝ) :=
      Rat.cast_le.mpr finite_vector_h4_tail_certificate.1
    apply (finite_sine_tail_interval_bound T _ _ rotation_finite_data_sound).trans
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hnum
  · have hnum : (intervalL4 (finiteSineTailInterval differenceFiniteData):ℝ) ≤ ((1/10000:ℚ):ℝ) :=
      Rat.cast_le.mpr finite_vector_h4_tail_certificate.2
    apply (finite_sine_tail_interval_bound T _ _ difference_finite_data_sound).trans
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hnum

end Lemniscate
