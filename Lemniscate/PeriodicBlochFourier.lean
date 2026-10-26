import Lemniscate.PeriodicBlochParity
import Lemniscate.PeriodicOddMatrix
import Lemniscate.PeriodicReflectionSplit

/-! Fourier entries of the actual Bloch differential operator on H4.
The parameter shifts the differential symbol, while the coefficient functions
and their ordinary derivatives are unchanged. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic OddArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleFourierH4 (m : ℤ) : circleH4Domain T :=
  ⟨fourierBasis (T := T) m, circle_fourier_mem_h4 T m⟩

theorem circle_shifted_first_basis (z : ℂ) (m : ℤ) :
    circleShiftedFirst T z (circleFourierH4 T m) =
      (circleFrequencyFactor T m+z) • fourierBasis (T := T) m := by
  change (circleH4Jet T (circleFourierH4 T m)).first+z • fourierBasis (T := T) m = _
  rw [circleFourierH4, circle_fourier_h4_jet]
  change circleFrequencyFactor T m • fourierBasis (T := T) m+z • fourierBasis (T := T) m = _
  module

theorem circle_shifted_second_basis (z : ℂ) (m : ℤ) :
    circleShiftedSecond T z (circleFourierH4 T m) =
      (circleFrequencyFactor T m+z)^2 • fourierBasis (T := T) m := by
  change (circleH4Jet T (circleFourierH4 T m)).second+
    (2*z) • (circleH4Jet T (circleFourierH4 T m)).first+
    z^2 • fourierBasis (T := T) m = _
  rw [circleFourierH4, circle_fourier_h4_jet]
  change (circleFrequencyFactor T m)^2 • fourierBasis (T := T) m+
    (2*z) • (circleFrequencyFactor T m • fourierBasis (T := T) m)+
    z^2 • fourierBasis (T := T) m = _
  module

theorem circle_shifted_fourth_basis (z : ℂ) (m : ℤ) :
    circleShiftedFourth T z (circleFourierH4 T m) =
      (circleFrequencyFactor T m+z)^4 • fourierBasis (T := T) m := by
  change (circleH4Jet T (circleFourierH4 T m)).fourth+
    (4*z) • (circleH4Jet T (circleFourierH4 T m)).third+
    (6*z^2) • (circleH4Jet T (circleFourierH4 T m)).second+
    (4*z^3) • (circleH4Jet T (circleFourierH4 T m)).first+
    z^4 • fourierBasis (T := T) m = _
  rw [circleFourierH4, circle_fourier_h4_jet]
  change (circleFrequencyFactor T m)^4 • fourierBasis (T := T) m+
    (4*z) • ((circleFrequencyFactor T m)^3 • fourierBasis (T := T) m)+
    (6*z^2) • ((circleFrequencyFactor T m)^2 • fourierBasis (T := T) m)+
    (4*z^3) • (circleFrequencyFactor T m • fourierBasis (T := T) m)+
    z^4 • fourierBasis (T := T) m = _
  module

theorem circle_bloch_basis_apply (h h₁ h₂ : C(AddCircle T, ℂ)) (α : ℝ) (m : ℤ) :
    circleBlochOperator T h h₁ h₂ α (circleFourierH4 T m) =
      (-4*(circleFrequencyFactor T m+(α:ℂ)*circleFrequencyFactor T 1)^4-42) •
        fourierBasis (T := T) m-
      (45*(circleFrequencyFactor T m+(α:ℂ)*circleFrequencyFactor T 1)^2) •
        circleMultiplyL2 T h (fourierBasis (T := T) m)-
      ((75/2)*(circleFrequencyFactor T m+(α:ℂ)*circleFrequencyFactor T 1)) •
        circleMultiplyL2 T h₁ (fourierBasis (T := T) m)+
      (15/2:ℂ) • circleMultiplyL2 T h₂ (fourierBasis (T := T) m) := by
  simp only [circleBlochOperator, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, circle_shifted_first_basis,
    circle_shifted_second_basis, circle_shifted_fourth_basis, map_smul]
  change (-4:ℂ) • _-45 • _-(75/2:ℂ) • _-42 • fourierBasis (T := T) m+
    (15/2:ℂ) • circleMultiplyL2 T h₂ (fourierBasis (T := T) m) = _
  module

noncomputable def circleBlochFourierEntry (h : C(AddCircle T, ℂ)) (α : ℝ) (n m : ℤ) : ℂ :=
  ((-4*(2*Real.pi/T)^4*((m:ℝ)+α)^4-42:ℝ):ℂ)*(if n = m then 1 else 0)+
  (((15/2:ℝ)*(2*Real.pi/T)^2*((n:ℝ)+α)*(7*((m:ℝ)+α)-((n:ℝ)+α)):ℝ):ℂ)*
    fourierCoeff h (n-m)

theorem circle_bloch_basis_fourier (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (α : ℝ) (n m : ℤ) :
    fourierCoeff (circleBlochOperator T h h₁ h₂ α (circleFourierH4 T m)) n =
      circleBlochFourierEntry T h α n m := by
  rw [circle_bloch_basis_apply]
  simp only [circle_fourierCoeff_add, circle_fourierCoeff_sub, circle_fourierCoeff_smul,
    circle_multiply_basis_fourier]
  rw [← circle_continuous_l2_fourier_basis, circle_continuous_l2_fourier,
    circle_continuous_fourier_mode, fourierCoeff_classical_deriv T h h₁ hh,
    fourierCoeff_classical_second T h h₁ h₂ hh hh₁]
  unfold circleBlochFourierEntry circleFrequencyFactor
  push_cast
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_four]
  ring

theorem circle_bloch_basis_pairing (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (α : ℝ) (n m : ℤ) :
    inner ℂ (fourierBasis (T := T) n)
      (circleBlochOperator T h h₁ h₂ α (circleFourierH4 T m)) =
        circleBlochFourierEntry T h α n m := by
  rw [← HilbertBasis.repr_apply_apply, fourierBasis_repr,
    circle_bloch_basis_fourier T h h₁ h₂ hh hh₁]

theorem circle_bloch_odd_symmetric_entry (h : C(AddCircle T, ℂ))
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (α : ℝ)
    (n m : ℤ) (hn : Odd n) (hm : Odd m) :
    (circleBlochFourierEntry T h α n m+conj (circleBlochFourierEntry T h α m n))/2 =
      (oddMatrixEntry α n m:ℂ) := by
  have hr4 : (2*Real.pi/T)^4 = thetaParameter^2 := by
    calc
      _ = ((2*Real.pi/T)^2)^2 := by ring
      _ = _ := by rw [hr]
  unfold circleBlochFourierEntry
  rw [hr4, hr, circle_odd_difference_coefficient T h thetaParameter nome hs hc n m hn hm,
    circle_odd_difference_coefficient T h thetaParameter nome hs hc m n hm hn]
  by_cases he : n = m
  · subst m
    simp only [oddMatrixEntry, ite_true, sub_self, Int.natAbs_zero, Nat.zero_div,
      mul_one, map_add, map_mul, Complex.conj_ofReal]
    push_cast
    ring
  · have hd : (m-n).natAbs = (n-m).natAbs := by
      have heq := congrArg Int.natAbs (show m-n = -(n-m) by omega)
      simpa only [Int.natAbs_neg] using heq
    simp only [oddMatrixEntry, if_neg he, if_neg (Ne.symm he), mul_zero, zero_add,
      map_mul, Complex.conj_ofReal, hd, oddEntryPolynomial]
    push_cast
    ring

theorem circle_bloch_odd_symmetric_pairing (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (α : ℝ)
    (n m : ℤ) (hn : Odd n) (hm : Odd m) :
    (inner ℂ (fourierBasis (T := T) n) (circleBlochOperator T h h₁ h₂ α (circleFourierH4 T m))+
      inner ℂ (circleBlochOperator T h h₁ h₂ α (circleFourierH4 T n))
        (fourierBasis (T := T) m))/2 = (oddMatrixEntry α n m:ℂ) := by
  rw [circle_bloch_basis_pairing T h h₁ h₂ hh hh₁ α n m,
    ← inner_conj_symm, circle_bloch_basis_pairing T h h₁ h₂ hh hh₁ α m n]
  exact circle_bloch_odd_symmetric_entry T h hs hc hr α n m hn hm

end Lemniscate
