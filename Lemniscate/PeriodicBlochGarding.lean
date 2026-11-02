import Lemniscate.PeriodicShiftedEnergy
import Lemniscate.PeriodicBlochPolynomial

/-! The shifted weak derivative estimates applied to the actual Bloch operator.
No Fourier coefficient formula or numerical matrix certificate is assumed. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleShiftedThird (z : ℂ) : circleH4Domain T →ₗ[ℂ] CircleL2 T :=
  circleH4Derivative T 2+(3*z) • circleH4Derivative T 1+
    (3*z^2) • circleH4Derivative T 0+z^3 • (circleH4Domain T).subtype

theorem circle_h4_shifted_derivative_chain (z : ℂ) (f : circleH4Domain T) :
    HasWeakCircleShiftedDeriv T z (f : CircleL2 T) (circleShiftedFirst T z f) ∧
    HasWeakCircleShiftedDeriv T z (circleShiftedFirst T z f) (circleShiftedSecond T z f) ∧
    HasWeakCircleShiftedDeriv T z (circleShiftedSecond T z f) (circleShiftedThird T z f) ∧
    HasWeakCircleShiftedDeriv T z (circleShiftedThird T z f) (circleShiftedFourth T z f) := by
  let J := circleH4Jet T f
  have hd₁ := circle_weak_deriv_add T _ _ _ _ J.hsecond
    (circle_weak_deriv_smul T z _ _ J.hfirst)
  have hd₂ := circle_weak_deriv_add T _ _ _ _
    (circle_weak_deriv_add T _ _ _ _ J.hthird
      (circle_weak_deriv_smul T (2*z) _ _ J.hsecond))
    (circle_weak_deriv_smul T (z^2) _ _ J.hfirst)
  have hd₃ := circle_weak_deriv_add T _ _ _ _
    (circle_weak_deriv_add T _ _ _ _
      (circle_weak_deriv_add T _ _ _ _ J.hfourth
        (circle_weak_deriv_smul T (3*z) _ _ J.hthird))
      (circle_weak_deriv_smul T (3*z^2) _ _ J.hsecond))
    (circle_weak_deriv_smul T (z^3) _ _ J.hfirst)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact circle_shifted_deriv_of_weak T z _ _ J.hfirst
  · change HasWeakCircleDeriv T (J.first+z • (f : CircleL2 T))
      (J.second+(2*z) • J.first+z^2 • (f : CircleL2 T)-
        z • (J.first+z • (f : CircleL2 T)))
    convert hd₁ using 1 <;> module
  · change HasWeakCircleDeriv T
      (J.second+(2*z) • J.first+z^2 • (f : CircleL2 T))
      (J.third+(3*z) • J.second+(3*z^2) • J.first+z^3 • (f : CircleL2 T)-
        z • (J.second+(2*z) • J.first+z^2 • (f : CircleL2 T)))
    convert hd₂ using 1 <;> module
  · change HasWeakCircleDeriv T
      (J.third+(3*z) • J.second+(3*z^2) • J.first+z^3 • (f : CircleL2 T))
      (J.fourth+(4*z) • J.third+(6*z^2) • J.second+(4*z^3) • J.first+
        z^4 • (f : CircleL2 T)-
        z • (J.third+(3*z) • J.second+(3*z^2) • J.first+z^3 • (f : CircleL2 T)))
    convert hd₃ using 1 <;> module

theorem circle_bloch_operator_energy (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) (α : ℝ) (f : circleH4Domain T) :
    (inner ℂ (f : CircleL2 T) (circleBlochOperator T h h₁ h₂ α f)).re =
      circleH2Energy T h h₂ (f : CircleL2 T)
        (circleShiftedFirst T ((α:ℂ)*circleFrequencyFactor T 1) f)
        (circleShiftedSecond T ((α:ℂ)*circleFrequencyFactor T 1) f) := by
  let z := (α:ℂ)*circleFrequencyFactor T 1
  have hz : conj z = -z := by
    simp only [z, map_mul, Complex.conj_ofReal, circle_frequency_factor_conj, mul_neg]
  rcases circle_h4_shifted_derivative_chain T z f with ⟨hf, hf₁, hf₂, hf₃⟩
  have hid : circleBlochOperator T h h₁ h₂ α f =
      circleLinearL2Expression T h h₁ h₂ (f : CircleL2 T)
        (circleShiftedFirst T z f) (circleShiftedSecond T z f) (circleShiftedFourth T z f) := by
    simp only [circleBlochOperator, circleLinearL2Expression, circleSymmetricL2Expression,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    change (-4:ℂ) • circleShiftedFourth T z f -
      (45:ℂ) • circleMultiplyL2 T h (circleShiftedSecond T z f)-
      (75/2:ℂ) • circleMultiplyL2 T h₁ (circleShiftedFirst T z f)-
      (42:ℂ) • (f : CircleL2 T)+
      (15/2:ℂ) • circleMultiplyL2 T h₂ (f : CircleL2 T) = _
    module
  rw [hid]
  exact circle_shifted_linear_energy T z hz h h₁ h₂ hh hh₁ hreal h₁real h₂real
    _ _ _ _ _ hf hf₁ hf₂ hf₃

theorem paper_bloch_operator_garding (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (α : ℝ) (f : circleH4Domain T) :
    (inner ℂ (f : CircleL2 T)
      (circleBlochOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) α f)).re ≤
        -2*‖circleShiftedSecond T ((α:ℂ)*circleFrequencyFactor T 1) f‖^2+
          (1719/8:ℝ)*‖(f : CircleL2 T)‖^2 := by
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
  rw [circle_bloch_operator_energy T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
    (circle_profile_square_deriv T q p hq) (circle_profile_square_second T q p hq hp he)
    h0real h1real h2real, circle_h2_energy_profile]
  have hz : conj ((α:ℂ)*circleFrequencyFactor T 1) = -((α:ℂ)*circleFrequencyFactor T 1) := by
    simp only [map_mul, Complex.conj_ofReal, circle_frequency_factor_conj, mul_neg]
  rcases circle_h4_shifted_derivative_chain T ((α:ℂ)*circleFrequencyFactor T 1) f with
    ⟨hf, hf₁, _, _⟩
  exact paper_shifted_energy_garding T _ hz q hqreal
    (circle_profile_uniform_norm T q p he hqreal hpreal).1 _ _ _ hf hf₁

end Lemniscate
