import Lemniscate.PeriodicBlochFourier

/-! Fourier entries of each coefficient of the actual Bloch operator.
Development source for the finite-dimensional energy estimate. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleBlochCoefficientEntry (h : C(AddCircle T, ℂ))
    (j : Fin 5) (n m : ℤ) : ℂ :=
  let r := (2*Real.pi/T)^2
  let d : ℂ := if n = m then 1 else 0
  let c := fourierCoeff h (n-m)
  ![((-4*r^2*(m:ℝ)^4-42:ℝ):ℂ)*d+
      (((15/2:ℝ)*r*(n:ℝ)*(7*(m:ℝ)-(n:ℝ)):ℝ):ℂ)*c,
    ((-16*r^2*(m:ℝ)^3:ℝ):ℂ)*d+
      ((r*((75/2:ℝ)*(n:ℝ)+(105/2:ℝ)*(m:ℝ)):ℝ):ℂ)*c,
    ((-24*r^2*(m:ℝ)^2:ℝ):ℂ)*d+((45*r:ℝ):ℂ)*c,
    ((-16*r^2*(m:ℝ):ℝ):ℂ)*d,
    ((-4*r^2:ℝ):ℂ)*d] j

theorem circle_bloch_coefficient_basis_fourier (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (j : Fin 5) (n m : ℤ) :
    fourierCoeff (circleBlochCoefficient T h h₁ h₂ j (circleFourierH4 T m)) n =
      circleBlochCoefficientEntry T h j n m := by
  have hb : fourierCoeff (fourierBasis (T := T) m) n = if n = m then 1 else 0 := by
    rw [← fourierBasis_repr, HilbertBasis.repr_apply_apply]
    exact orthonormal_iff_ite.mp (fourierBasis (T := T)).orthonormal n m
  fin_cases j
  · change fourierCoeff (circleBlochCoefficient T h h₁ h₂ (0:Fin 5) (circleFourierH4 T m)) n =
      circleBlochCoefficientEntry T h 0 n m
    rw [circle_bloch_coefficient_zero T h h₁ h₂, ← circle_bloch_at_zero,
      circle_bloch_basis_fourier T h h₁ h₂ hh hh₁]
    simp only [circleBlochCoefficientEntry, Matrix.cons_val_zero, circleBlochFourierEntry,
      add_zero]
    push_cast
    ring
  · change fourierCoeff (circleBlochCoefficient T h h₁ h₂ (1:Fin 5) (circleFourierH4 T m)) n =
      circleBlochCoefficientEntry T h 1 n m
    rw [circle_bloch_coefficient_one_apply T h h₁ h₂, circleFourierH4, circle_fourier_h4_jet]
    change fourierCoeff (circleFrequencyFactor T 1 •
      ((-16:ℂ) • ((circleFrequencyFactor T m)^3 • fourierBasis (T := T) m)-
        (90:ℂ) • circleMultiplyL2 T h (circleFrequencyFactor T m • fourierBasis (T := T) m)-
        (75/2:ℂ) • circleMultiplyL2 T h₁ (fourierBasis (T := T) m))) n = _
    simp only [map_smul, circle_fourierCoeff_smul, circle_fourierCoeff_sub,
      circle_multiply_basis_fourier, hb, fourierCoeff_classical_deriv T h h₁ hh,
      circleBlochCoefficientEntry, Matrix.cons_val_one]
    unfold circleFrequencyFactor
    push_cast
    ring_nf
    simp only [Complex.I_sq, Complex.I_pow_four]
    ring
  · change fourierCoeff (circleBlochCoefficient T h h₁ h₂ (2:Fin 5) (circleFourierH4 T m)) n =
      circleBlochCoefficientEntry T h 2 n m
    rw [circle_bloch_coefficient_two_apply T h h₁ h₂, circleFourierH4, circle_fourier_h4_jet]
    change fourierCoeff ((circleFrequencyFactor T 1)^2 •
      ((-24:ℂ) • ((circleFrequencyFactor T m)^2 • fourierBasis (T := T) m)-
        (45:ℂ) • circleMultiplyL2 T h (fourierBasis (T := T) m))) n = _
    simp only [circle_fourierCoeff_smul, circle_fourierCoeff_sub,
      circle_multiply_basis_fourier, hb, circleBlochCoefficientEntry,
      Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons]
    unfold circleFrequencyFactor
    push_cast
    ring_nf
    simp only [Complex.I_sq, Complex.I_pow_four]
    ring
  · change fourierCoeff (circleBlochCoefficient T h h₁ h₂ (3:Fin 5) (circleFourierH4 T m)) n =
      circleBlochCoefficientEntry T h 3 n m
    rw [circle_bloch_coefficient_three_apply T h h₁ h₂, circleFourierH4, circle_fourier_h4_jet]
    change fourierCoeff ((circleFrequencyFactor T 1)^3 •
      ((-16:ℂ) • (circleFrequencyFactor T m • fourierBasis (T := T) m))) n = _
    simp only [circle_fourierCoeff_smul, hb, circleBlochCoefficientEntry,
      Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons]
    unfold circleFrequencyFactor
    push_cast
    ring_nf
    simp only [Complex.I_sq, Complex.I_pow_four]
    ring
  · change fourierCoeff (circleBlochCoefficient T h h₁ h₂ (4:Fin 5) (circleFourierH4 T m)) n =
      circleBlochCoefficientEntry T h 4 n m
    rw [circle_bloch_coefficient_four_apply T h h₁ h₂]
    change fourierCoeff ((circleFrequencyFactor T 1)^4 •
      ((-4:ℂ) • fourierBasis (T := T) m)) n = _
    simp only [circle_fourierCoeff_smul, hb, circleBlochCoefficientEntry,
      Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons]
    unfold circleFrequencyFactor
    push_cast
    ring_nf
    simp only [Complex.I_sq, Complex.I_pow_four]
    ring

theorem circle_bloch_coefficient_basis_pairing (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (j : Fin 5) (n m : ℤ) :
    inner ℂ (fourierBasis (T := T) n)
      (circleBlochCoefficient T h h₁ h₂ j (circleFourierH4 T m)) =
        circleBlochCoefficientEntry T h j n m := by
  rw [← HilbertBasis.repr_apply_apply, fourierBasis_repr,
    circle_bloch_coefficient_basis_fourier T h h₁ h₂ hh hh₁]

end Lemniscate
