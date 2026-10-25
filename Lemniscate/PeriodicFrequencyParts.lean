import Lemniscate.PeriodicOddCoefficients
import Lemniscate.PeriodicReflectionSplit
import Lemniscate.PeriodicBoundedMultiplier

/-! Orthogonal even/odd Fourier-frequency projections on the actual L2 space,
including preservation of the weak H4 domain. This is distinct from reflection. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

noncomputable def evenFrequencySymbol (n : ℤ) : ℂ := if Odd n then 0 else 1

theorem even_frequency_symbol_bound (n : ℤ) : ‖evenFrequencySymbol n‖ ≤ 1 := by
  unfold evenFrequencySymbol
  split_ifs <;> norm_num

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleEvenFrequencyPart : CircleL2 T →L[ℂ] CircleL2 T :=
  circleBoundedMultiplier T evenFrequencySymbol 1 (by norm_num) even_frequency_symbol_bound

noncomputable def circleOddFrequencyPart : CircleL2 T →L[ℂ] CircleL2 T :=
  ContinuousLinearMap.id ℂ (CircleL2 T) - circleEvenFrequencyPart T

theorem circle_even_frequency_part_fourier (f : CircleL2 T) (n : ℤ) :
    fourierCoeff (circleEvenFrequencyPart T f) n = if Odd n then 0 else fourierCoeff f n := by
  rw [circleEvenFrequencyPart, circle_bounded_multiplier_fourier, evenFrequencySymbol]
  split_ifs <;> simp

theorem circle_odd_frequency_part_fourier (f : CircleL2 T) (n : ℤ) :
    fourierCoeff (circleOddFrequencyPart T f) n = if Odd n then fourierCoeff f n else 0 := by
  change fourierCoeff (f-circleEvenFrequencyPart T f) n = _
  rw [circle_fourierCoeff_sub, circle_even_frequency_part_fourier]
  split_ifs <;> simp

theorem circle_frequency_parts_sum (f : CircleL2 T) :
    circleEvenFrequencyPart T f + circleOddFrequencyPart T f = f := by
  change circleEvenFrequencyPart T f + (f-circleEvenFrequencyPart T f) = f
  abel

theorem circle_even_frequency_part_sector (f : CircleL2 T) (n : ℤ) :
    fourierCoeff (circleEvenFrequencyPart T f) (2*n+1) = 0 := by
  rw [circle_even_frequency_part_fourier, if_pos (show Odd (2*n+1) from ⟨n, by ring⟩)]

theorem circle_odd_frequency_part_sector (f : CircleL2 T) :
    InCircleOddSector T (circleOddFrequencyPart T f) := by
  intro n hn
  rw [circle_odd_frequency_part_fourier, if_neg hn]

theorem circle_frequency_sectors_orthogonal (f g : CircleL2 T)
    (hf : ∀ n : ℤ, fourierCoeff f (2*n+1) = 0) (hg : InCircleOddSector T g) :
    inner ℂ f g = 0 := by
  rw [circle_inner_fourier]
  have hz (n : ℤ) : conj (fourierCoeff f n)*fourierCoeff g n = 0 := by
    by_cases hn : Odd n
    · obtain ⟨i, rfl⟩ := (odd_frequency_range n).mpr hn
      rw [hf, map_zero, zero_mul]
    · rw [hg n hn, mul_zero]
  simp only [hz, tsum_zero]

theorem circle_frequency_parts_norm_sq (f : CircleL2 T) :
    ‖f‖^2 = ‖circleEvenFrequencyPart T f‖^2+‖circleOddFrequencyPart T f‖^2 := by
  have hz := circle_frequency_sectors_orthogonal T _ _
    (circle_even_frequency_part_sector T f) (circle_odd_frequency_part_sector T f)
  have hz' : inner ℂ (circleOddFrequencyPart T f) (circleEvenFrequencyPart T f) = 0 := by
    rw [← inner_conj_symm, hz, map_zero]
  have he : inner ℂ f f = inner ℂ (circleEvenFrequencyPart T f) (circleEvenFrequencyPart T f)+
      inner ℂ (circleOddFrequencyPart T f) (circleOddFrequencyPart T f) := by
    conv_lhs => rw [← circle_frequency_parts_sum T f]
    simp only [inner_add_left, inner_add_right, hz, hz', zero_add, add_zero]
  calc
    ‖f‖^2 = (inner ℂ f f).re := norm_sq_eq_re_inner (𝕜 := ℂ) f
    _ = _ := by
      rw [he, Complex.add_re]
      exact congrArg₂ (fun a b : ℝ => a+b)
        (norm_sq_eq_re_inner (𝕜 := ℂ) (circleEvenFrequencyPart T f)).symm
        (norm_sq_eq_re_inner (𝕜 := ℂ) (circleOddFrequencyPart T f)).symm

theorem circle_even_frequency_part_weak_deriv (f g : CircleL2 T)
    (hfg : HasWeakCircleDeriv T f g) :
    HasWeakCircleDeriv T (circleEvenFrequencyPart T f) (circleEvenFrequencyPart T g) := by
  apply weak_circle_deriv_of_fourier
  intro n
  rw [circle_even_frequency_part_fourier, circle_even_frequency_part_fourier,
    fourier_of_weak_circle_deriv T f g hfg]
  split_ifs <;> simp

theorem circle_even_frequency_part_mem_h4 (f : circleH4Domain T) :
    InCircleH4 T (circleEvenFrequencyPart T (f : CircleL2 T)) := by
  apply circle_h4_of_fourth_fourier T _ (circleEvenFrequencyPart T (circleH4Jet T f).fourth)
  intro n
  rw [circle_even_frequency_part_fourier, circle_even_frequency_part_fourier,
    circle_h4_fourth_fourier]
  split_ifs <;> simp

noncomputable def circleEvenFrequencyPartH4 (f : circleH4Domain T) : circleH4Domain T :=
  ⟨circleEvenFrequencyPart T (f : CircleL2 T), circle_even_frequency_part_mem_h4 T f⟩

noncomputable def circleOddFrequencyPartH4 (f : circleH4Domain T) : circleH4Domain T :=
  f-circleEvenFrequencyPartH4 T f

theorem circle_even_frequency_part_h4_coe (f : circleH4Domain T) :
    (circleEvenFrequencyPartH4 T f : CircleL2 T) = circleEvenFrequencyPart T (f : CircleL2 T) := rfl

theorem circle_odd_frequency_part_h4_coe (f : circleH4Domain T) :
    (circleOddFrequencyPartH4 T f : CircleL2 T) = circleOddFrequencyPart T (f : CircleL2 T) := rfl

theorem circle_frequency_h4_parts_sum (f : circleH4Domain T) :
    circleEvenFrequencyPartH4 T f + circleOddFrequencyPartH4 T f = f := by
  apply Subtype.ext
  exact circle_frequency_parts_sum T (f : CircleL2 T)

theorem circle_even_frequency_part_h4_first (f : circleH4Domain T) :
    (circleH4Jet T (circleEvenFrequencyPartH4 T f)).first =
      circleEvenFrequencyPart T (circleH4Jet T f).first :=
  weak_circle_deriv_unique T _ _ _ (circleH4Jet T (circleEvenFrequencyPartH4 T f)).hfirst
    (circle_even_frequency_part_weak_deriv T _ _ (circleH4Jet T f).hfirst)

theorem circle_even_frequency_part_h4_second (f : circleH4Domain T) :
    (circleH4Jet T (circleEvenFrequencyPartH4 T f)).second =
      circleEvenFrequencyPart T (circleH4Jet T f).second := by
  apply weak_circle_deriv_unique T _ _ _ (circleH4Jet T (circleEvenFrequencyPartH4 T f)).hsecond
  rw [circle_even_frequency_part_h4_first]
  exact circle_even_frequency_part_weak_deriv T _ _ (circleH4Jet T f).hsecond

theorem circle_even_frequency_part_h4_fourth (f : circleH4Domain T) :
    (circleH4Jet T (circleEvenFrequencyPartH4 T f)).fourth =
      circleEvenFrequencyPart T (circleH4Jet T f).fourth := by
  apply circle_fourier_ext T
  intro n
  rw [circle_h4_fourth_fourier, circle_even_frequency_part_fourier, circle_h4_fourth_fourier]
  change (circleFrequencyFactor T n)^4 *
    fourierCoeff (circleEvenFrequencyPart T (f : CircleL2 T)) n = _
  rw [circle_even_frequency_part_fourier]
  split_ifs <;> simp

end Lemniscate
