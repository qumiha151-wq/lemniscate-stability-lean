import Lemniscate.PeriodicSymmetryPairing

/-! The exact normalized adjoint vector inherits the odd reflection parity
and even Fourier support of the rotation vector. These conclusions follow
from uniqueness and operator commutation, not from Galerkin data. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_adjoint_pairing_even_frequency (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (ho : ∀ i : ℤ, fourierCoeff h (2*i+1) = 0) (e ψ : CircleL2 T)
    (he : ∀ i : ℤ, fourierCoeff e (2*i+1) = 0)
    (hψ : inner ℂ ψ e = 1 ∧ ∀ f : circleH4Domain T,
      inner ℂ ψ (circleH4Operator T h h₁ h₂ f) = 0)
    (huniq : ∀ ψ' : CircleL2 T, (inner ℂ ψ' e = 1 ∧ ∀ f : circleH4Domain T,
      inner ℂ ψ' (circleH4Operator T h h₁ h₂ f) = 0) → ψ' = ψ) :
    circleEvenFrequencyPart T ψ = ψ := by
  apply huniq
  constructor
  · rw [circle_even_frequency_part_selfadjoint, circle_even_frequency_part_eq_self T e he]
    exact hψ.1
  · intro f
    rw [circle_even_frequency_part_selfadjoint,
      ← circle_h4_operator_even_frequency_part T h h₁ h₂ hh hh₁ ho]
    exact hψ.2 (circleEvenFrequencyPartH4 T f)

theorem circle_adjoint_pairing_reflect (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n) (e ψ : CircleL2 T)
    (he : circleReflect T e = -e)
    (hψ : inner ℂ ψ e = 1 ∧ ∀ f : circleH4Domain T,
      inner ℂ ψ (circleH4Operator T h h₁ h₂ f) = 0)
    (huniq : ∀ ψ' : CircleL2 T, (inner ℂ ψ' e = 1 ∧ ∀ f : circleH4Domain T,
      inner ℂ ψ' (circleH4Operator T h h₁ h₂ f) = 0) → ψ' = ψ) :
    circleReflect T ψ = -ψ := by
  have hfix : -circleReflect T ψ = ψ := by
    apply huniq
    constructor
    · rw [inner_neg_left, circle_reflect_selfadjoint, he, inner_neg_right, neg_neg]
      exact hψ.1
    · intro f
      rw [inner_neg_left, circle_reflect_selfadjoint,
        ← circle_h4_operator_reflect_of_even T h h₁ h₂ hh hh₁ hs, hψ.2, neg_zero]
  simpa only [neg_neg] using congrArg Neg.neg hfix

theorem circle_even_sine_sector_of_symmetries (ψ : CircleL2 T)
    (hr : circleReflect T ψ = -ψ) (hp : circleEvenFrequencyPart T ψ = ψ) :
    InCircleEvenSineSector T ψ := by
  constructor
  · intro n
    have hn : fourierCoeff (-ψ) n = -fourierCoeff ψ n := by
      simpa only [neg_one_smul, neg_one_mul] using circle_fourierCoeff_smul T (-1) ψ n
    calc
      _ = fourierCoeff (circleReflect T ψ) n := (circle_reflect_fourier T ψ n).symm
      _ = _ := by rw [hr, hn]
  · intro i
    have hz := circle_even_frequency_part_sector T ψ i
    rwa [hp] at hz

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ i : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*i+1) = 0)
    (hr : (2*Real.pi/T)^2 = thetaParameter)

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_single_period_adjoint_pairing_sector (ψ : CircleL2 T)
    (hψ : inner ℂ ψ (circleUnitRotation T q p) = 1 ∧ ∀ f : circleH4Domain T,
      inner ℂ ψ (circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) f) = 0) :
    InCircleEvenSineSector T ψ := by
  obtain ⟨φ, hφ, huniq⟩ :=
    paper_single_period_adjoint_pairing T q p hq hp he hqreal hpreal hs hc ho hr
  have heq : ψ = φ := huniq ψ hψ
  subst φ
  apply circle_even_sine_sector_of_symmetries T ψ
  · exact circle_adjoint_pairing_reflect T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circle_profile_square_deriv T q p hq) (circle_profile_square_second T q p hq hp he)
      hs (circleUnitRotation T q p) ψ (circle_unit_rotation_reflect T q p hq hs) hψ huniq
  · exact circle_adjoint_pairing_even_frequency T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (circle_profile_square_deriv T q p hq) (circle_profile_square_second T q p hq hp he)
      ho (circleUnitRotation T q p) ψ (circle_unit_rotation_no_odd T q p hq ho) hψ huniq

include hq hp he hqreal hpreal hs hc ho hr in
theorem paper_single_period_adjoint_vector_sector (ψ : circleH4Domain T)
    (hnorm : inner ℂ (ψ : CircleL2 T) (circleUnitRotation T q p) = 1)
    (hzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0) :
    InCircleEvenSineSector T (ψ : CircleL2 T) := by
  apply paper_single_period_adjoint_pairing_sector T q p hq hp he hqreal hpreal hs hc ho hr
  refine ⟨hnorm, ?_⟩
  intro f
  have h0real : ∀ x, conj ((q^2 : C(AddCircle T, ℂ)) x) = (q^2 : C(AddCircle T, ℂ)) x := by
    intro x
    change conj ((q x)^2) = (q x)^2
    simp only [map_pow, hqreal]
  have h1real : ∀ x, conj (((2:ℂ) • (q*p)) x) = ((2:ℂ) • (q*p)) x := by
    intro x
    change conj (2*(q x*p x)) = 2*(q x*p x)
    simp only [map_mul, map_ofNat, hqreal, hpreal]
  have h2real : ∀ x, conj ((1-(3:ℂ) • (q^4) : C(AddCircle T, ℂ)) x) =
      (1-(3:ℂ) • (q^4) : C(AddCircle T, ℂ)) x := by
    intro x
    change conj (1-3*(q x)^4) = 1-3*(q x)^4
    simp only [map_sub, map_mul, map_one, map_ofNat, map_pow, hqreal]
  rw [← inner_conj_symm, circle_h4_formal_adjoint_green T (q^2) ((2:ℂ) • (q*p))
    (1-(3:ℂ) • (q^4)) (circle_profile_square_deriv T q p hq)
    (circle_profile_square_second T q p hq hp he) h0real h1real h2real f ψ,
    hzero, inner_zero_right, map_zero]

end Profile
end Lemniscate
