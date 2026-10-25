import Lemniscate.PeriodicAdjointNeutral

/-! Pairing identities for reflection and frequency projection, and the
corresponding symmetries of the actual normalized rotation vector. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_reflect_selfadjoint (f g : CircleL2 T) :
    inner ℂ (circleReflect T f) g = inner ℂ f (circleReflect T g) := by
  calc
    _ = inner ℂ (circleReflect T f) (circleReflect T (circleReflect T g)) := by
      rw [circle_reflect_involutive]
    _ = _ := circle_reflect_inner T f (circleReflect T g)

theorem circle_even_frequency_part_selfadjoint (f g : CircleL2 T) :
    inner ℂ (circleEvenFrequencyPart T f) g = inner ℂ f (circleEvenFrequencyPart T g) := by
  rw [circle_inner_fourier, circle_inner_fourier]
  apply tsum_congr
  intro n
  rw [circle_even_frequency_part_fourier, circle_even_frequency_part_fourier]
  by_cases hn : Odd n <;> simp [hn]

theorem circle_even_frequency_part_eq_self (f : CircleL2 T)
    (hf : ∀ i : ℤ, fourierCoeff f (2*i+1) = 0) : circleEvenFrequencyPart T f = f := by
  apply circle_fourier_ext T
  intro n
  rw [circle_even_frequency_part_fourier]
  by_cases hn : Odd n
  · obtain ⟨i, hi⟩ := (odd_frequency_range n).mpr hn
    rw [if_pos hn, ← hi, hf]
  · rw [if_neg hn]

theorem circle_profile_rotation_reflect (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n) :
    circleReflect T (circleContinuousL2 T (q*p)) = -circleContinuousL2 T (q*p) := by
  apply circle_fourier_ext T
  intro n
  have hd := circle_deriv_reflection_parity T (q^2) ((2:ℂ) • (q*p))
    (circle_profile_square_deriv T q p hq) 1 (by simpa only [one_mul] using hs) n
  simp only [circle_continuous_fourier_smul, neg_one_mul] at hd
  have hn : fourierCoeff (-circleContinuousL2 T (q*p)) n =
      -fourierCoeff (circleContinuousL2 T (q*p)) n := by
    simpa only [neg_one_smul, neg_one_mul] using
      circle_fourierCoeff_smul T (-1) (circleContinuousL2 T (q*p)) n
  rw [circle_reflect_fourier, hn, circle_continuous_l2_fourier, circle_continuous_l2_fourier]
  linear_combination (1/2:ℂ)*hd

theorem circle_profile_rotation_no_odd (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p)
    (ho : ∀ i : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*i+1) = 0) (i : ℤ) :
    fourierCoeff (circleContinuousL2 T (q*p)) (2*i+1) = 0 := by
  have hd := fourierCoeff_classical_deriv T (q^2) ((2:ℂ) • (q*p))
    (circle_profile_square_deriv T q p hq) (2*i+1)
  rw [circle_continuous_fourier_smul, ho, mul_zero] at hd
  rw [circle_continuous_l2_fourier]
  linear_combination (1/2:ℂ)*hd

theorem circle_unit_rotation_reflect (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n) :
    circleReflect T (circleUnitRotation T q p) = -circleUnitRotation T q p := by
  rw [circleUnitRotation, circle_reflect_smul, circle_profile_rotation_reflect T q p hq hs,
    smul_neg]

theorem circle_unit_rotation_no_odd (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p)
    (ho : ∀ i : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*i+1) = 0) (i : ℤ) :
    fourierCoeff (circleUnitRotation T q p) (2*i+1) = 0 := by
  rw [circleUnitRotation, circle_fourierCoeff_smul, circle_profile_rotation_no_odd T q p hq ho,
    mul_zero]

end Lemniscate
