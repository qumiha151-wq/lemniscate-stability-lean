import Lemniscate.PeriodicFrequencyParts

/-! Even/odd Fourier-frequency splitting commutes with the actual H4 operator
when the coefficient has no odd frequencies. Cross terms are consequently zero. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_even_frequency_part_basis (m : ℤ) :
    circleEvenFrequencyPart T (fourierBasis (T := T) m) =
      evenFrequencySymbol m • fourierBasis (T := T) m := by
  apply circle_fourier_ext T
  intro n
  rw [circle_even_frequency_part_fourier, circle_fourierCoeff_smul]
  have hb : fourierCoeff (fourierBasis (T := T) m) n = if n = m then 1 else 0 := by
    rw [← circle_continuous_l2_fourier_basis, circle_continuous_l2_fourier,
      circle_continuous_fourier_mode]
  rw [hb]
  by_cases he : n = m
  · subst n
    simp only [ite_true, evenFrequencySymbol, mul_one]
  · simp only [if_neg he, mul_zero]
    split_ifs <;> rfl

theorem circle_even_frequency_part_multiply_basis (h : C(AddCircle T, ℂ))
    (ho : ∀ i : ℤ, fourierCoeff h (2*i+1) = 0) (m : ℤ) :
    circleEvenFrequencyPart T (circleMultiplyL2 T h (fourierBasis (T := T) m)) =
      circleMultiplyL2 T h (circleEvenFrequencyPart T (fourierBasis (T := T) m)) := by
  apply circle_fourier_ext T
  intro n
  rw [circle_even_frequency_part_fourier, circle_multiply_basis_fourier,
    circle_even_frequency_part_basis, map_smul, circle_fourierCoeff_smul,
    circle_multiply_basis_fourier]
  by_cases hn : Odd n <;> by_cases hm : Odd m
  · simp [hn, hm, evenFrequencySymbol]
  · have hd : Odd (n-m) := by
      rw [Int.odd_iff] at hn hm ⊢
      omega
    obtain ⟨i, hi⟩ := (odd_frequency_range (n-m)).mpr hd
    rw [← hi, ho]
    simp [hn, hm, evenFrequencySymbol]
  · have hd : Odd (n-m) := by
      rw [Int.odd_iff] at hn hm ⊢
      omega
    obtain ⟨i, hi⟩ := (odd_frequency_range (n-m)).mpr hd
    rw [← hi, ho]
    simp [hn, hm, evenFrequencySymbol]
  · simp [hn, hm, evenFrequencySymbol]

theorem circle_even_frequency_part_multiply (h : C(AddCircle T, ℂ))
    (ho : ∀ i : ℤ, fourierCoeff h (2*i+1) = 0) (f : CircleL2 T) :
    circleEvenFrequencyPart T (circleMultiplyL2 T h f) =
      circleMultiplyL2 T h (circleEvenFrequencyPart T f) := by
  let F := (circleEvenFrequencyPart T).comp (circleMultiplyL2 T h)
  let G := (circleMultiplyL2 T h).comp (circleEvenFrequencyPart T)
  have hb (m : ℤ) : F (fourierBasis (T := T) m) = G (fourierBasis (T := T) m) :=
    circle_even_frequency_part_multiply_basis T h ho m
  have hF := ((fourierBasis (T := T)).hasSum_repr f).mapL F
  have hG := ((fourierBasis (T := T)).hasSum_repr f).mapL G
  simp only [map_smul, hb] at hF
  simp only [map_smul] at hG
  exact hF.unique hG

theorem circle_deriv_no_odd_frequencies (h h₁ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (ho : ∀ i : ℤ, fourierCoeff h (2*i+1) = 0) (i : ℤ) :
    fourierCoeff h₁ (2*i+1) = 0 := by
  rw [fourierCoeff_classical_deriv T h h₁ hh, ho, mul_zero]

theorem circle_h4_operator_even_frequency_part (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (ho : ∀ i : ℤ, fourierCoeff h (2*i+1) = 0) (f : circleH4Domain T) :
    circleH4Operator T h h₁ h₂ (circleEvenFrequencyPartH4 T f) =
      circleEvenFrequencyPart T (circleH4Operator T h h₁ h₂ f) := by
  have ho₁ := circle_deriv_no_odd_frequencies T h h₁ hh ho
  have ho₂ := circle_deriv_no_odd_frequencies T h₁ h₂ hh₁ ho₁
  simp only [circle_h4_operator_apply, circleLinearL2Expression, circleSymmetricL2Expression,
    circle_even_frequency_part_h4_first, circle_even_frequency_part_h4_second,
    circle_even_frequency_part_h4_fourth, circle_even_frequency_part_h4_coe,
    map_add, map_sub, map_smul, circle_even_frequency_part_multiply T h ho,
    circle_even_frequency_part_multiply T h₁ ho₁, circle_even_frequency_part_multiply T h₂ ho₂]

theorem circle_h4_operator_odd_frequency_part (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (ho : ∀ i : ℤ, fourierCoeff h (2*i+1) = 0) (f : circleH4Domain T) :
    circleH4Operator T h h₁ h₂ (circleOddFrequencyPartH4 T f) =
      circleOddFrequencyPart T (circleH4Operator T h h₁ h₂ f) := by
  rw [circleOddFrequencyPartH4, map_sub, circle_h4_operator_even_frequency_part T h h₁ h₂ hh hh₁ ho]
  rfl

theorem circle_h4_operator_frequency_energy_split (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (ho : ∀ i : ℤ, fourierCoeff h (2*i+1) = 0) (f : circleH4Domain T) :
    inner ℂ (f : CircleL2 T) (circleH4Operator T h h₁ h₂ f) =
      inner ℂ (circleEvenFrequencyPart T (f : CircleL2 T))
        (circleH4Operator T h h₁ h₂ (circleEvenFrequencyPartH4 T f)) +
      inner ℂ (circleOddFrequencyPart T (f : CircleL2 T))
        (circleH4Operator T h h₁ h₂ (circleOddFrequencyPartH4 T f)) := by
  let A := circleH4Operator T h h₁ h₂
  let e := circleEvenFrequencyPartH4 T f
  let o := circleOddFrequencyPartH4 T f
  have heo : inner ℂ (e : CircleL2 T) (A o) = 0 := by
    rw [show A o = circleOddFrequencyPart T (A f) from
      circle_h4_operator_odd_frequency_part T h h₁ h₂ hh hh₁ ho f]
    exact circle_frequency_sectors_orthogonal T _ _
      (circle_even_frequency_part_sector T _) (circle_odd_frequency_part_sector T _)
  have hoe : inner ℂ (o : CircleL2 T) (A e) = 0 := by
    rw [show A e = circleEvenFrequencyPart T (A f) from
      circle_h4_operator_even_frequency_part T h h₁ h₂ hh hh₁ ho f]
    have hz := circle_frequency_sectors_orthogonal T _ _
      (circle_even_frequency_part_sector T (A f))
      (circle_odd_frequency_part_sector T (f : CircleL2 T))
    change inner ℂ (circleOddFrequencyPart T (f : CircleL2 T))
      (circleEvenFrequencyPart T (A f)) = 0
    rw [← inner_conj_symm, hz, map_zero]
  have he : e+o = f := circle_frequency_h4_parts_sum T f
  have he' := congrArg (fun z : circleH4Domain T => inner ℂ (z : CircleL2 T) (A z)) he
  change inner ℂ (f : CircleL2 T) (A f) =
    inner ℂ (e : CircleL2 T) (A e) + inner ℂ (o : CircleL2 T) (A o)
  simpa only [Submodule.coe_add, map_add, inner_add_left, inner_add_right,
    heo, hoe, zero_add, add_zero] using he'.symm

theorem circle_even_frequency_part_constraint (f : CircleL2 T)
    (horth : inner ℂ (circleSineConstraintVector T) f = 0) :
    inner ℂ (circleSineConstraintVector T) (circleEvenFrequencyPart T f) = 0 := by
  have hz := circle_frequency_sectors_orthogonal T (circleSineConstraintVector T)
    (circleOddFrequencyPart T f) (circle_sine_constraint_coeff_odd T)
    (circle_odd_frequency_part_sector T f)
  rw [← circle_frequency_parts_sum T f, inner_add_right, hz, add_zero] at horth
  exact horth

end Lemniscate
