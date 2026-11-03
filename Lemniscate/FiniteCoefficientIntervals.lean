import Lemniscate.HeadIntervalOperations

/-! Interval enclosures for all five actual real Fourier coefficient matrices.
No matrix eigenvalue or floating-point approximation is used. -/
namespace Lemniscate.CoarseArithmetic

def coefficientSquaredPeriodInput : Interval :=
  roundInterval 30 (mul finitePeriodInput finitePeriodInput)

def coefficientPeriodProductInput (i k : Fin 31) : Interval :=
  roundInterval 30 (mul finitePeriodInput (finiteDifferenceInput i k))

def finiteBlochCoefficientInput (j : Fin 5) : Matrix (Fin 31) (Fin 31) Interval := fun i k =>
  let n : ℚ := (evenHeadFrequency i:ℤ)
  let m : ℚ := (evenHeadFrequency k:ℤ)
  let d : ℚ := if i = k then 1 else 0
  let r₂ := coefficientSquaredPeriodInput
  let rc := coefficientPeriodProductInput i k
  match j.val with
  | 0 => add (add (scale r₂ (-4*m^4*d)) (point (-42*d)))
      (scale rc ((15/2:ℚ)*n*(7*m-n)))
  | 1 => add (scale r₂ (-16*m^3*d)) (scale rc ((75/2:ℚ)*n+(105/2:ℚ)*m))
  | 2 => add (scale r₂ (-24*m^2*d)) (scale rc 45)
  | 3 => scale r₂ (-16*m*d)
  | _ => scale r₂ (-4*d)

theorem coefficient_squared_period_input_sound :
    Contains coefficientSquaredPeriodInput (lemniscateFrequencySquared^2) := by
  simpa only [coefficientSquaredPeriodInput, pow_two] using
    roundInterval_sound 30 _ _
      (mul_sound _ _ _ _ finite_period_input_sound finite_period_input_sound)

theorem coefficient_period_product_input_sound (i k : Fin 31) :
    Contains (coefficientPeriodProductInput i k)
      (lemniscateFrequencySquared*fourierCoefficient lemniscateFrequencySquared nome
        ((evenHeadFrequency i-evenHeadFrequency k).natAbs/2)) :=
  roundInterval_sound 30 _ _
    (mul_sound _ _ _ _ finite_period_input_sound (finite_difference_input_sound i k))

theorem finite_bloch_coefficient_input_sound (j : Fin 5) :
    MatrixContains (finiteBlochCoefficientInput j) (evenBlochCoefficientMatrix lemniscateFrequencySquared nome j) := by
  intro i k
  let n : ℚ := (evenHeadFrequency i:ℤ)
  let m : ℚ := (evenHeadFrequency k:ℤ)
  let d : ℚ := if i = k then 1 else 0
  let c : ℝ := fourierCoefficient lemniscateFrequencySquared nome ((evenHeadFrequency i-evenHeadFrequency k).natAbs/2)
  have hS (a : ℚ) := scale_sound _ _ a coefficient_squared_period_input_sound
  have hP (a : ℚ) := scale_sound _ _ a (coefficient_period_product_input_sound i k)
  fin_cases j
  · have h := add_sound _ _ _ _
      (add_sound _ _ _ _ (hS (-4*m^4*d)) (point_sound (-42*d)))
      (hP ((15/2:ℚ)*n*(7*m-n)))
    have heq : lemniscateFrequencySquared^2*((-4*m^4*d:ℚ):ℝ)+((-42*d:ℚ):ℝ)+
        (lemniscateFrequencySquared*c)*(((15/2:ℚ)*n*(7*m-n):ℚ):ℝ) =
          evenBlochCoefficientMatrix lemniscateFrequencySquared nome 0 i k := by
      by_cases hik : i = k <;> norm_num [evenBlochCoefficientMatrix, n, m, d, c, hik] <;> push_cast <;> ring
    rw [heq] at h
    exact h
  · have h := add_sound _ _ _ _ (hS (-16*m^3*d)) (hP ((75/2:ℚ)*n+(105/2:ℚ)*m))
    have heq : lemniscateFrequencySquared^2*((-16*m^3*d:ℚ):ℝ)+
        (lemniscateFrequencySquared*c)*((((75/2:ℚ)*n+(105/2:ℚ)*m:ℚ):ℝ)) =
          evenBlochCoefficientMatrix lemniscateFrequencySquared nome 1 i k := by
      by_cases hik : i = k <;> norm_num [evenBlochCoefficientMatrix, n, m, d, c, hik] <;> push_cast <;> ring
    rw [heq] at h
    exact h
  · have h := add_sound _ _ _ _ (hS (-24*m^2*d)) (hP 45)
    have heq : lemniscateFrequencySquared^2*((-24*m^2*d:ℚ):ℝ)+(lemniscateFrequencySquared*c)*(45:ℚ) =
        evenBlochCoefficientMatrix lemniscateFrequencySquared nome 2 i k := by
      by_cases hik : i = k <;> norm_num [evenBlochCoefficientMatrix, n, m, d, c, hik] <;> push_cast <;> ring
    rw [heq] at h
    exact h
  · have h := hS (-16*m*d)
    have heq : lemniscateFrequencySquared^2*((-16*m*d:ℚ):ℝ) =
        evenBlochCoefficientMatrix lemniscateFrequencySquared nome 3 i k := by
      by_cases hik : i = k <;> norm_num [evenBlochCoefficientMatrix, n, m, d, c, hik] <;> push_cast <;> ring
    rw [heq] at h
    exact h
  · have h := hS (-4*d)
    have heq : lemniscateFrequencySquared^2*((-4*d:ℚ):ℝ) =
        evenBlochCoefficientMatrix lemniscateFrequencySquared nome 4 i k := by
      by_cases hik : i = k <;> norm_num [evenBlochCoefficientMatrix, n, m, d, c, hik] <;> push_cast <;> ring
    rw [heq] at h
    exact h

end Lemniscate.CoarseArithmetic
