import Lemniscate.PeriodicFrequencyOperator
import Lemniscate.PeriodicEvenEnergy
import Lemniscate.PeriodicOddOperatorEnergy

/-! Full single-period H4 coercivity on the rotation-orthogonal complement.
Both frequency sectors and their operator cross terms are proved internally.
The concrete Jacobi profile's Fourier and period data remain explicit. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_h4_operator_frequency_split_bound (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ i : ℤ, fourierCoeff h (2*i+1) = 0)
    (hr : (2*Real.pi/T)^2 = thetaParameter) (f : circleH4Domain T)
    (horth : inner ℂ (circleSineConstraintVector T) (f : CircleL2 T) = 0) :
    (inner ℂ (f : CircleL2 T) (circleH4Operator T h h₁ h₂ f)).re ≤
      -(21/4:ℝ)*‖circleEvenFrequencyPart T (f : CircleL2 T)‖^2 -
        6*‖circleOddFrequencyPart T (f : CircleL2 T)‖^2 := by
  have he := circle_h4_operator_even_frequencies_dissipative T h h₁ h₂
    hh hh₁ hreal h₁real h₂real hs hc hr (circleEvenFrequencyPartH4 T f)
    (circle_even_frequency_part_sector T (f : CircleL2 T))
    (circle_even_frequency_part_constraint T (f : CircleL2 T) horth)
  have ho' := circle_h4_operator_odd_dissipative T h h₁ h₂
    hh hh₁ hreal h₁real h₂real hs hc hr (circleOddFrequencyPartH4 T f)
    (circle_odd_frequency_part_sector T (f : CircleL2 T))
  rw [circle_h4_operator_frequency_energy_split T h h₁ h₂ hh hh₁ ho, Complex.add_re]
  simpa only [circle_even_frequency_part_h4_coe, circle_odd_frequency_part_h4_coe,
    sub_eq_add_neg, neg_mul] using add_le_add he ho'

theorem circle_h4_operator_rotation_complement_dissipative (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ i : ℤ, fourierCoeff h (2*i+1) = 0)
    (hr : (2*Real.pi/T)^2 = thetaParameter) (f : circleH4Domain T)
    (horth : inner ℂ (circleSineConstraintVector T) (f : CircleL2 T) = 0) :
    (inner ℂ (f : CircleL2 T) (circleH4Operator T h h₁ h₂ f)).re ≤
      -(21/4:ℝ)*‖(f : CircleL2 T)‖^2 := by
  have hb := circle_h4_operator_frequency_split_bound T h h₁ h₂
    hh hh₁ hreal h₁real h₂real hs hc ho hr f horth
  rw [circle_frequency_parts_norm_sq T (f : CircleL2 T)]
  nlinarith [sq_nonneg ‖circleOddFrequencyPart T (f : CircleL2 T)‖]

theorem paper_h4_operator_rotation_complement_dissipative (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ i : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*i+1) = 0)
    (hr : (2*Real.pi/T)^2 = thetaParameter) (f : circleH4Domain T)
    (horth : inner ℂ (circleContinuousL2 T (q*p)) (f : CircleL2 T) = 0) :
    (inner ℂ (f : CircleL2 T)
      (circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) f)).re ≤
        -(21/4:ℝ)*‖(f : CircleL2 T)‖^2 := by
  apply circle_h4_operator_rotation_complement_dissipative T (q^2) ((2:ℂ) • (q*p))
    (1-(3:ℂ) • (q^4)) (circle_profile_square_deriv T q p hq)
    (circle_profile_square_second T q p hq hp he)
    _ _ _ hs hc ho hr f (circle_sine_profile_constraint T q p hq hs hc ho _ horth)
  · intro x
    change conj ((q x)^2) = (q x)^2
    simp only [map_pow, hqreal]
  · intro x
    change conj (2*(q x*p x)) = 2*(q x*p x)
    simp only [map_mul, map_ofNat, hqreal, hpreal]
  · intro x
    change conj (1-3*(q x)^4) = 1-3*(q x)^4
    simp only [map_sub, map_mul, map_one, map_ofNat, map_pow, hqreal]

end Lemniscate
