import Lemniscate.PeriodicConjugateOperator
import Lemniscate.PeriodicAdjointSymmetry

/-! The exact adjoint zero vector is real-valued and belongs to the even sine
sector. A common unit phase gives real antisymmetric Fourier coefficients,
as required before the paper's Householder construction. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_unit_rotation_real (q p : C(AddCircle T, ℂ))
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x) :
    circleConjugate T (circleUnitRotation T q p) = circleUnitRotation T q p := by
  have hqp : ∀ x, conj ((q*p) x) = (q*p) x := by
    intro x
    change conj (q x*p x) = q x*p x
    rw [map_mul, hqreal, hpreal]
  rw [circleUnitRotation, circle_conjugate_smul, map_inv₀, Complex.conj_ofReal,
    circle_conjugate_continuous_real T (q*p) hqp]

theorem circle_real_sine_phase_fourier (f : CircleL2 T)
    (hreal : circleConjugate T f = f) (hs : InCircleEvenSineSector T f) (n : ℤ) :
    conj (fourierCoeff ((-I) • f) n) = fourierCoeff ((-I) • f) n := by
  have hc := congrArg (fun g : CircleL2 T => fourierCoeff g n) hreal
  rw [circle_conjugate_fourier, hs.1, map_neg] at hc
  simp only [circle_fourierCoeff_smul, map_mul, map_neg, Complex.conj_I, neg_neg]
  linear_combination (-I)*hc

theorem circle_sine_phase_sector (f : CircleL2 T) (hs : InCircleEvenSineSector T f) :
    InCircleEvenSineSector T ((-I) • f) := by
  constructor
  · intro n
    rw [circle_fourierCoeff_smul, circle_fourierCoeff_smul, hs.1, mul_neg]
  · intro i
    rw [circle_fourierCoeff_smul, hs.2, mul_zero]

theorem circle_common_phase_inner (f g : CircleL2 T) :
    inner ℂ ((-I) • f) ((-I) • g) = inner ℂ f g := by
  rw [inner_smul_left, inner_smul_right]
  simp only [map_neg, Complex.conj_I, neg_neg]
  rw [← mul_assoc]
  norm_num

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
theorem paper_single_period_adjoint_real_sector :
    ∃! ψ : circleH4Domain T,
      inner ℂ (ψ : CircleL2 T) (circleUnitRotation T q p) = 1 ∧
      circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0 ∧
      circleConjugate T (ψ : CircleL2 T) = (ψ : CircleL2 T) ∧
      InCircleEvenSineSector T (ψ : CircleL2 T) := by
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
  obtain ⟨ψ, hψ, huniq⟩ :=
    paper_single_period_adjoint_pairing T q p hq hp he hqreal hpreal hs hc ho hr
  have hrealψ := circle_adjoint_pairing_real T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
    h0real h1real h2real (circleUnitRotation T q p) ψ
    (circle_unit_rotation_real T q p hqreal hpreal) hψ huniq
  have hsector :=
    paper_single_period_adjoint_pairing_sector T q p hq hp he hqreal hpreal hs hc ho hr ψ hψ
  obtain ⟨g, hg, hAg⟩ := circle_adjoint_zero_of_pairing T (q^2) ((2:ℂ) • (q*p))
    (1-(3:ℂ) • (q^4)) (circle_profile_square_deriv T q p hq)
    (circle_profile_square_second T q p hq hp he) h0real h1real h2real ψ hψ.2
  have hnorm : inner ℂ (g : CircleL2 T) (circleUnitRotation T q p) = 1 := by
    rw [hg]
    exact hψ.1
  refine ⟨g, ⟨hnorm, hAg, ?_, ?_⟩, ?_⟩
  · simpa only [hg] using hrealψ
  · simpa only [hg] using hsector
  · intro g' hg'
    obtain ⟨u, _, hu⟩ :=
      paper_single_period_adjoint_vector T q p hq hp he hqreal hpreal hs hc ho hr
    exact (hu g' ⟨hg'.1, hg'.2.1⟩).trans (hu g ⟨hnorm, hAg⟩).symm

end Profile
end Lemniscate
