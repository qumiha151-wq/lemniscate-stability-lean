import Lemniscate.PeriodicOddEnergy
import Lemniscate.PeriodicH4Operator

/-! The -6 odd-frequency bound for the actual unbounded periodic operator
on its full H4 domain. Concrete Jacobi Fourier data remain explicit hypotheses. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_h4_operator_odd_dissipative (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (f : circleH4Domain T)
    (hf : InCircleOddSector T (f : CircleL2 T)) :
    (inner ℂ (f : CircleL2 T) (circleH4Operator T h h₁ h₂ f)).re ≤
      -6*‖(f : CircleL2 T)‖^2 := by
  rw [circle_h4_operator_energy T h h₁ h₂ hh hh₁ hreal h₁real h₂real]
  exact circle_odd_weak_energy_dissipative T h h₁ h₂ hh hh₁ hs hc hr
    (f : CircleL2 T) (circleH4Jet T f).first (circleH4Jet T f).second hf
    (circleH4Jet T f).hfirst (circleH4Jet T f).hsecond

theorem paper_h4_operator_odd_dissipative (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (f : circleH4Domain T)
    (hf : InCircleOddSector T (f : CircleL2 T)) :
    (inner ℂ (f : CircleL2 T)
      (circleH4Operator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) f)).re ≤
        -6*‖(f : CircleL2 T)‖^2 := by
  apply circle_h4_operator_odd_dissipative T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
    (circle_profile_square_deriv T q p hq) (circle_profile_square_second T q p hq hp he)
    _ _ _ hs hc hr f hf
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
